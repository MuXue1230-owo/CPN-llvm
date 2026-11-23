#include "Sema.h"
#include "llvm/ADT/ScopeExit.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/IR/Intrinsics.h"

using namespace cpn;
using llvm::StringRef;

namespace {
std::string boundParameter(size_t I) {
  return "$contract.parameter." + std::to_string(I);
}

bool sameExpression(const Node &A, const Node &B) {
  return A.K == B.K && A.Text == B.Text && A.Type == B.Type &&
         A.Definition == B.Definition &&
         A.ExplicitApplication == B.ExplicitApplication &&
         A.Settings == B.Settings && A.Children.size() == B.Children.size() &&
         A.TemplateArgs.size() == B.TemplateArgs.size() &&
         std::equal(A.Children.begin(), A.Children.end(), B.Children.begin(),
                    sameExpression) &&
         std::equal(A.TemplateArgs.begin(), A.TemplateArgs.end(),
                    B.TemplateArgs.begin(), sameExpression);
}

bool trivialPredicate(const Node &Clause) {
  const Node &Expr = Clause.Children.front();
  return Expr.K == Node::Name && Expr.Text == "true";
}

void bindPredicateEnvironment(Frame &Check) {
  const auto &F = *Check.F;
  Check.Opt = F.Defaults.Configuration;
  Check.LookupLimit = F.Defaults.Through;
  Check.Prefix = F.DefaultPrefix;
  Check.Env = F.DefaultEnv;
}

void bindPredicateParameter(std::map<std::string, Value> &Names,
                            const Function &F, size_t I, Value Arg,
                            bool Entry) {
  Names.emplace(boundParameter(I), Arg);
  const auto &Original = F.DefaultParams[I].Text;
  if (!Original.empty() && (Entry || Original != "return_value"))
    Names.emplace(Original, std::move(Arg));
}
} // namespace

std::string cpn::parameterBinding(const Node &D, size_t I) {
  const auto &Name = D.Params[I].Text;
  return Name.empty() ? "$arg." + std::to_string(I) : Name;
}

void cpn::normalizeContracts(Node &D) {
  auto Bind = [&](auto &&Visit, Node &Expr, bool Ensures) -> void {
    if (Expr.K == Node::Name && !(Ensures && Expr.Text == "return_value")) {
      for (size_t I = 0; I < D.Params.size(); ++I)
        if (!D.Params[I].Text.empty() && D.Params[I].Text == Expr.Text) {
          Expr.Text = Expr.At.Text = boundParameter(I);
          break;
        }
    }
    for (auto &Child : Expr.Children)
      Visit(Visit, Child, Ensures);
    for (auto &Arg : Expr.TemplateArgs)
      Visit(Visit, Arg, Ensures);
  };
  for (auto &Clause : D.Contracts)
    Bind(Bind, Clause.Children.front(), Clause.Text == "ensures");
}

bool cpn::sameContracts(const Node &A, const Node &B) {
  return A.Contracts.size() == B.Contracts.size() &&
         std::equal(A.Contracts.begin(), A.Contracts.end(), B.Contracts.begin(),
                    sameExpression);
}

void Context::proveValueOverride(Function &Derived, Function &Base,
                                 const BasePath &Path) {
  const auto Pointer = llvm::PointerType::getUnqual(C);
  for (bool Entry : {true, false}) {
    if (!Entry && Derived.Result == "never")
      continue;
    auto &Premise = Entry ? Base : Derived;
    auto &Goal = Entry ? Derived : Base;
    auto Key = Entry ? "requires" : "ensures";
    auto NeedsProof = [&](const Node &Clause) {
      return Clause.Text == Key && !trivialPredicate(Clause);
    };
    if (llvm::none_of(Goal.Decl.Contracts, NeedsProof))
      continue;

    llvm::SmallVector<llvm::Type *> Types(
        Derived.IR->getFunctionType()->params());
    bool AggregateResult = aggregate(Derived.Result);
    StringRef ResultType = Derived.Result;
    bool ReferenceResult = ResultType.consume_back("&");
    if (ReferenceResult)
      ResultType.consume_back("&");
    auto *PreparedType =
        ReferenceResult ? Pointer : ir(Derived.Result, Derived.Decl.At);
    bool HasPreparedArgument =
        !Entry && !AggregateResult && !PreparedType->isVoidTy();
    unsigned PreparedArgument = Types.size();
    if (HasPreparedArgument)
      Types.push_back(PreparedType);
    auto *Scratch = llvm::Function::Create(
        llvm::FunctionType::get(llvm::Type::getVoidTy(C), Types, false),
        llvm::GlobalValue::PrivateLinkage, "", M);
    auto Discard = llvm::scope_exit([&] { Scratch->eraseFromParent(); });

    Frame Probe(*this, &Derived, Scratch);
    Probe.TypeQuery = true;
    Probe.TracksStorage = false;
    Probe.B.SetInsertPoint(Probe.block("entry"));
    Probe.bindParams();
    // Lower the actual inherited view. Shared virtual-base offsets remain
    // symbolic inputs read from the receiver's layout.
    auto BaseReceiver = Probe.baseView(Probe.Self, Path);
    Value Prepared{unconst(ResultType.str())};
    if (AggregateResult)
      Prepared.Address = Scratch->getArg(0);
    else if (HasPreparedArgument) {
      if (ReferenceResult)
        Prepared.Address = Scratch->getArg(PreparedArgument);
      else
        Prepared.IR = Scratch->getArg(PreparedArgument);
    }
    Prepared.Readonly = true;

    auto *Valid = Probe.block("compatible"), *Invalid = Probe.block("invalid");
    llvm::SmallPtrSet<llvm::Instruction *, 8> PremiseFailures;
    auto MarkFailure = [&](llvm::Instruction &I) {
      I.setMetadata("cpn.override.failure", llvm::MDNode::get(C, {}));
    };
    auto EmitConditions = [&](Function &Declaration, bool Assume) {
      EnterDefinition Site(*this, Declaration.Defaults);
      Frame Check(*this, &Declaration, Scratch);
      bindPredicateEnvironment(Check);
      Check.TypeQuery = true;
      Check.TracksStorage = false;
      Check.Self = &Declaration == &Base ? BaseReceiver : Probe.Self;
      Check.B.SetInsertPoint(Probe.B.GetInsertBlock());
      auto &Names = Check.Scopes.front().Names;
      auto ReceiverType = Check.Self.Type;
      if (Check.Self.Readonly)
        ReceiverType = qualifyConst(ReceiverType);
      Names["this"] = {ReceiverType + "*", Check.Self.Address};
      for (size_t I = 0; I < Declaration.Params.size(); ++I) {
        auto Input =
            Probe.Scopes.front().Names.at(parameterBinding(Derived.Decl, I));
        StringRef Parameter = Declaration.Params[I];
        bool Reference = Parameter.consume_back("&");
        if (Reference)
          Parameter.consume_back("&");
        Input.Readonly = Declaration.DefaultParams[I].Const ||
                         (Reference && Parameter.starts_with("const<"));
        bindPredicateParameter(Names, Declaration, I, std::move(Input), Entry);
      }
      if (!Entry && Prepared.Type != "void" && Prepared.Type != "never")
        Names["return_value"] = Prepared;
      unsigned Ordinal = 0;
      for (const auto &Clause : Declaration.Decl.Contracts) {
        ++Ordinal;
        if (!NeedsProof(Clause))
          continue;
        auto *Result = Check.evaluatePredicate(Clause, Declaration.Name,
                                               Ordinal, "prove", true);
        auto *Next = Check.block("next");
        Check.B.CreateCondBr(Result, Next, Assume ? Valid : Invalid);
        Check.B.SetInsertPoint(Next);
      }
      Probe.B.SetInsertPoint(Check.B.GetInsertBlock());
      for (auto &Block : *Scratch)
        for (auto &I : Block)
          if (auto *Call = llvm::dyn_cast<llvm::CallBase>(&I);
              Call && Call->getIntrinsicID() == llvm::Intrinsic::trap) {
            if (Assume)
              PremiseFailures.insert(&I);
            else if (!PremiseFailures.contains(&I))
              MarkFailure(I);
          }
    };
    EmitConditions(Premise, true);
    EmitConditions(Goal, false);
    Probe.B.CreateBr(Valid);
    Probe.B.SetInsertPoint(Valid);
    Probe.B.CreateRetVoid();
    Probe.B.SetInsertPoint(Invalid);
    MarkFailure(*Probe.B.CreateCall(
        llvm::Intrinsic::getOrInsertDeclaration(&M, llvm::Intrinsic::trap)));
    Probe.B.CreateUnreachable();
    if (!proveNoContractFailure(*Scratch))
      fail(
          Derived.Decl.At,
          std::string(
              "invalid override of inherited virtual slot: cannot establish ") +
              (Entry ? "precondition" : "postcondition") +
              " implication for '" + Base.Name + "'");
  }
}

void Frame::requireObserver(const EffectBound &Bound, const Token &At,
                            const Function *Target) {
  if (!InPredicate)
    return;
  if (!Bound ||
      llvm::any_of(
          *Bound,
          [](StringRef Effect) { return !Effect.starts_with("read:"); }) ||
      (Target &&
       (Target->Decl.Foreign || Target->Result == "never" || Target->MayWhole ||
        !Target->Consumes.empty() || !Target->Initializes.empty())))
    fail(At,
         "contract predicate calls require a closed read-only effect bound");
  if (Target && Target->Defaults.Configuration.ContractsEnabled &&
      Target->Defaults.Configuration.ContractValidation == "check" &&
      !llvm::all_of(Target->Decl.Contracts, trivialPredicate))
    fail(At, "contract observer has an unestablished checked condition");
  if (Target && U.hasCheckedInvariant(*Target))
    fail(At, "contract observer has an unestablished checked invariant");
}

void Frame::requirePredicateCleanup(const std::string &Type, const Token &At) {
  if (!InPredicate)
    return;
  const auto T = unconst(Type);
  if (StringRef(T).ends_with("]")) {
    if (!StringRef(T).ends_with("[0]"))
      requirePredicateCleanup(element(T), At);
    return;
  }
  auto R = U.Records.find(T);
  if (R == U.Records.end())
    return;
  if (auto I = U.Overloads.find(T + "::$drop"); I != U.Overloads.end()) {
    auto *D = I->second.front();
    requireObserver(D->Effects, At, D);
  }
  for (const auto &Field : R->second.Fields)
    requirePredicateCleanup(Field.Type, At);
  if (auto I = U.Variants.find(T); I != U.Variants.end())
    for (const auto &Case : I->second)
      for (const auto &Member : U.Cases.at(Case).Types)
        requirePredicateCleanup(Member, At);
}

llvm::Value *Frame::evaluatePredicate(const Node &Clause, StringRef Declaration,
                                      unsigned Ordinal, StringRef Mode,
                                      bool ValidateOnly, bool OwnBoundary) {
  if (!ValidateOnly && Mode != "check" && Mode != "prove")
    return nullptr;
  llvm::BasicBlock *Before = nullptr;
  if (IR && !ValidateOnly && Mode == "prove") {
    Before = B.GetInsertBlock();
    auto *Proof = block("contract.prove");
    B.CreateBr(Proof);
    B.SetInsertPoint(Proof);
  }
  llvm::SmallPtrSet<const llvm::Instruction *, 32> Existing;
  if (IR && !ValidateOnly && OwnBoundary && !Before)
    for (auto &Block : *IR)
      for (const auto &Inst : Block)
        Existing.insert(&Inst);
  llvm::SaveAndRestore Predicate(InPredicate, true);
  auto V = eval(Clause.Children.front());
  if (V.Type != "bool")
    fail(Clause.At, "contract predicate requires bool");
  auto *Condition = load(V).IR;
  endExpression();
  if (!ValidateOnly) {
    auto *Known = llvm::dyn_cast_or_null<llvm::ConstantInt>(Condition);
    auto Label =
        Declaration.str() + " " + Clause.Text + " #" + std::to_string(Ordinal);
    if (!IR && (!Known || Known->isZero()))
      fail(Clause.At, "cannot establish " + Label);
    if (IR && (Before || !Known || Known->isZero())) {
      auto *Check = B.CreateCondBr(Condition, block("contract.pass"),
                                   block("contract.fail"));
      B.SetInsertPoint(Check->getSuccessor(1));
      auto *Trap = B.CreateCall(
          llvm::Intrinsic::getOrInsertDeclaration(&U.M, llvm::Intrinsic::trap));
      if (Before)
        U.ContractProofs.push_back({Before, Check->getSuccessor(0),
                                    Check->getSuccessor(1), Clause.At,
                                    std::move(Label)});
      else {
        Trap->setMetadata(
            OwnBoundary ? "cpn.boundary.effects" : "cpn.effect",
            llvm::MDNode::get(U.C, llvm::MDString::get(U.C, "trap:contract")));
        Trap->setMetadata(
            "cpn.contract",
            llvm::MDNode::get(U.C, llvm::MDString::get(U.C, Label)));
      }
      B.CreateUnreachable();
      B.SetInsertPoint(Check->getSuccessor(0));
    }
  }
  if (IR && !ValidateOnly && OwnBoundary && !Before) {
    auto *Marker = llvm::MDNode::get(U.C, {});
    for (auto &Block : *IR)
      for (auto &Inst : Block)
        if (!Existing.contains(&Inst))
          Inst.setMetadata("cpn.boundary", Marker);
  }
  return Condition;
}

void Frame::checkContracts(bool Entry, Value Result, bool ValidateOnly,
                           bool *MayTrap) {
  if (F->Decl.Contracts.empty())
    return;
  const auto &Policy = F->Defaults.Configuration;
  const auto &Mode = Policy.ContractValidation;
  if (!ValidateOnly && (!Live || !Policy.ContractsEnabled ||
                        (Mode != "check" && Mode != "prove")))
    return;
  Frame Check(U, F, IR);
  bindPredicateEnvironment(Check);
  Check.TypeQuery = ValidateOnly;
  Check.Transaction = Transaction;
  Check.Active = Active;
  Check.Extents = Extents;
  Check.ConstantMembersAlive = ConstantMembersAlive;
  Check.FieldFlags = FieldFlags;
  Check.BaseLayer = BaseLayer;
  if (IR)
    Check.B.SetInsertPoint(B.GetInsertBlock());
  auto &Names = Check.Scopes.front().Names;
  auto &Parameters = Scopes.front().Names;
  if (F->Decl.Settings.count("closure"))
    Names = Scopes[1].Names;
  if (!(Entry && F->Decl.K == Node::Constructor)) {
    Check.Self = Self;
    Check.ConstantReceiver = ConstantReceiver;
    if (auto This = Parameters.find("this"); This != Parameters.end())
      Names.insert(*This);
  }
  for (size_t I = 0; I < F->Params.size(); ++I) {
    if (auto Arg = Parameters.find(parameterBinding(F->Decl, I));
        Arg != Parameters.end())
      bindPredicateParameter(Names, *F, I, Arg->second, Entry);
  }
  if (!Entry && F->Result != "void" && F->Result != "never") {
    Result.Readonly = true;
    if (StringRef(F->Result).ends_with("&") && Result.Address)
      Result.IR = nullptr;
    Names["return_value"] = std::move(Result);
  }
  unsigned I = 0;
  bool OwnBoundary = IR == F->IR || IR == F->BaseIR || IR == F->ImportAdapter;
  for (const auto &Clause : F->Decl.Contracts) {
    ++I;
    if (Entry == (Clause.Text == "requires")) {
      auto *Condition = Check.evaluatePredicate(Clause, F->Name, I, Mode,
                                                ValidateOnly, OwnBoundary);
      if (MayTrap) {
        const auto *Known =
            llvm::dyn_cast_or_null<llvm::ConstantInt>(Condition);
        *MayTrap |= !Known || !Known->isOne();
      }
    }
  }
  if (IR)
    B.SetInsertPoint(Check.B.GetInsertBlock());
}

void Context::bindContracts(Function &D) {
  if (D.ContractsBound || D.Decl.Contracts.empty())
    return;
  if (D.Defaults.Configuration.ContractValidation == "trusted" &&
      !D.Defaults.Configuration.TrustedAssumptions)
    fail(D.Decl.At,
         "trusted contract validation requires contracts.trusted_assumptions");
  D.ContractsBound = true;
  auto *ProbeType = D.IR->getFunctionType();
  // Probe the prepared designation through its declared borrow origins.
  // Unattributed results remain unknown regions in a checked predicate.
  bool BorrowedResult = carriesBorrow(D.Result);
  if (BorrowedResult) {
    llvm::SmallVector<llvm::Type *> Types(ProbeType->params());
    Types.push_back(llvm::PointerType::getUnqual(C));
    ProbeType =
        llvm::FunctionType::get(ProbeType->getReturnType(), Types, false);
  }
  auto *Scratch = llvm::Function::Create(
      ProbeType, llvm::GlobalValue::PrivateLinkage, "", M);
  auto *ProbedResult =
      BorrowedResult ? Scratch->getArg(Scratch->arg_size() - 1) : nullptr;
  Frame Probe(*this, &D, Scratch);
  Probe.TypeQuery = true;
  Probe.B.SetInsertPoint(Probe.block("entry"));
  Probe.bindParams();
  if (D.Decl.Settings.count("closure"))
    Probe.bindCaptures();
  bool MayTrap = false;
  Probe.checkContracts(true, {}, true, &MayTrap);
  Value Result{D.Result};
  if (D.Result != "void" && D.Result != "never") {
    auto ResultType = StringRef(D.Result);
    if (ResultType.consume_back("&")) {
      ResultType.consume_back("&");
      Result.Type = unconst(ResultType.str());
      Result.Address = ProbedResult;
    } else {
      Result.Address = Probe.allocate(Result.Type, D.Decl.At);
      if (ProbedResult)
        Probe.B.CreateStore(ProbedResult, Result.Address);
    }
  }
  Probe.checkContracts(false, Result, true, &MayTrap);
  const auto &Policy = D.Defaults.Configuration;
  if (Policy.ContractsEnabled && Policy.ContractValidation == "check") {
    Probe.B.CreateUnreachable();
    D.PredicateEffects = bindPredicateEffects(D, *Scratch, ProbedResult);
    if (MayTrap)
      D.PredicateEffects.insert("trap:contract");
  }
  Scratch->eraseFromParent();
}
