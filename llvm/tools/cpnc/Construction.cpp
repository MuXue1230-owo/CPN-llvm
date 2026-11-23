#include "Sema.h"
#include "llvm/ADT/ScopeExit.h"
#include "llvm/ADT/SetVector.h"
using namespace cpn;
namespace {
const Node *site(const Node &N, bool Conditional = false) {
  if (N.K == Node::Delegate) {
    if (Conditional)
      fail(N.At, "delegation must be unconditional");
    return &N;
  }
  if (N.K == Node::Object || N.K == Node::Tail || N.K == Node::Lambda)
    return nullptr;
  bool Nested = Conditional || N.K == Node::If || N.K == Node::Switch ||
                N.K == Node::Match || N.K == Node::For || N.K == Node::While ||
                N.K == Node::Do;
  const Node *Found = nullptr;
  for (auto &C : N.Children)
    if (auto *S = site(C, Nested)) {
      if (Found)
        fail(S->At, "only one direct delegation is permitted");
      Found = S;
    }
  return Found;
}
} // namespace
Construction::Construction(Frame &Em, Function &Root, Value Obj,
                           const Node *Tail, Frame *Caller)
    : Object(Obj), TailFrame(Caller) {
  Object.BaseView |= Em.BaseLayer;
  if (Object.BaseView)
    Frontier = Em.U.Records.at(Obj.Type).VirtualCount;
  for (auto &F : Em.U.Records.at(Obj.Type).Fields)
    Order.push_back(F.Decl.Text);
  auto add = [&](const Node &Body, Function *Owner) {
    for (auto &N : Body.Children)
      if (N.K == Node::Init) {
        auto K = Em.initSlot(N);
        if (std::find(Order.begin(), Order.end(), K) == Order.end())
          fail(N.At, "unknown initialization target '" + K + "'");
        if (!Explicit.emplace(K, Producer{Owner, &N}).second)
          fail(N.At, "duplicate initialization producer");
      }
  };
  if (Tail)
    add(*Tail, nullptr);
  Function *D = &Root;
  while (D) {
    if (llvm::any_of(Chain, [&](auto &P) { return P.first == D; }))
      fail(D->Decl.At, "cyclic constructor delegation");
    auto &Body = D->Decl.Children.front();
    add(Body, D);
    auto *Site = site(Body);
    Chain.emplace_back(D, Site);
    if (!Site)
      break;
    auto &Candidates = Em.U.Overloads.at(Obj.Type + "::$ctor");
    std::vector<Function *> Viable;
    for (auto *C : Candidates)
      if (Site->Children.size() <= C->Params.size() &&
          (Site->Children.size() == C->Params.size() ||
           !C->Decl.Params[Site->Children.size()].Children.empty()))
        Viable.push_back(C);
    if (Viable.size() == 1) {
      D = Viable.front();
      continue;
    }
    // Type-check the delegate arguments in the source activation. Discard the
    // probe block; its instructions never enter the execution schedule.
    auto *FT = llvm::FunctionType::get(Em.B.getVoidTy(), false);
    auto *Tmp = llvm::Function::Create(FT, llvm::GlobalValue::InternalLinkage,
                                       "cpn.probe", Em.U.M);
    Frame Probe(Em.U, D, Tmp);
    Probe.TypeQuery = true;
    Probe.B.SetInsertPoint(Probe.block("entry"));
    Probe.Self = {Obj.Type, nullptr, llvm::PoisonValue::get(Em.B.getPtrTy())};
    for (size_t I = 0; I < D->Params.size(); ++I) {
      auto T = D->Params[I];
      while (llvm::StringRef(T).ends_with("&"))
        T.pop_back();
      Probe.Scopes[0].Names[D->Decl.Params[I].Text] = {
          T, nullptr, Probe.allocate(T, Site->At)};
    }
    std::vector<Value> Actual;
    for (auto &A : Site->Children)
      Actual.push_back(Probe.eval(A));
    D = Probe.select("$ctor", *Site, Actual, Probe.Self);
    Tmp->eraseFromParent();
  }
  findReservations(Em);
  if (Em.IR && (!Reserved.empty() || Em.U.Whole)) {
    Cursor = Em.allocate("i32", Root.Decl.At);
    publish(Em);
  }
}
bool Construction::needsDelegate(const Frame &F) const {
  for (auto &[D, Site] : Chain)
    if (D == F.F)
      return Site && !F.HasDelegated;
  return false;
}
void Construction::advance(Frame &Current) {
  auto &R = Current.U.Records.at(Object.Type);
  auto enterLayer = [&] {
    if (Current.IR)
      Current.installTables(Object);
    else
      Current.installConstantTables(Object, Current.F->Decl.At);
  };
  if (Frontier == R.Bases.size())
    enterLayer();
  while (Frontier < Order.size()) {
    auto &F = R.Fields[Frontier];
    if (Reserved.count(F.Decl.Text))
      return;
    auto It = Explicit.find(F.Decl.Text);
    Frame *Source = &Current;
    const std::vector<Node> *Args = &F.Decl.Children;
    if (It != Explicit.end()) {
      auto &P = It->second;
      if (P.Owner && !Activations.count(P.Owner))
        return;
      Source = P.Owner ? Activations.at(P.Owner) : TailFrame;
      Args = &P.Source->Children;
    }
    if (Current.IR)
      Source->B.SetInsertPoint(Current.B.GetInsertBlock());
    auto *Address =
        Current.IR ? Source->fieldAddress(Object, Frontier) : nullptr;
    llvm::SaveAndRestore Receiver(Source->ConstantReceiver,
                                  Current.IR ? nullptr : &Object);
    auto Previous = Source->Self;
    auto *PreviousTxn = Source->Transaction;
    Source->Transaction = this;
    Source->Self = Object;
    Local Earlier;
    Earlier.Names["this"] = {Object.Type + "*", Object.Address};
    for (size_t I = 0; I < R.Fields.size(); ++I) {
      auto &Member = R.Fields[I];
      Earlier.Names[Member.Decl.Text] =
          I >= Frontier ? Value{}
          : Current.IR
              ? Value{Member.Type, nullptr, Source->fieldAddress(Object, I)}
              : Source->constantField(Object, I, Member.Decl.At);
    }
    // Constructor parameters shadow members. Body-local declarations never
    // participate in the declarative initializer environment.
    auto Old = std::move(Source->Scopes);
    if (It != Explicit.end() && !It->second.Owner) {
      Source->Scopes = Old;
      Source->Scopes.push_back(std::move(Earlier));
    } else if (It != Explicit.end()) {
      Source->Scopes = {std::move(Earlier), Old.front()};
    } else {
      Source->Scopes = {std::move(Earlier)};
    }
    llvm::SaveAndRestore Policy(Source->Opt);
    llvm::SaveAndRestore Limit(Source->LookupLimit);
    if (It == Explicit.end() && F.DefaultSite) {
      Source->Opt = F.DefaultSite->Configuration;
      Source->LookupLimit = F.DefaultSite->Through;
    }
    size_t Mark = Source->Temps.size();
    if (!Current.IR && Frontier < R.Bases.size()) {
      auto Base = Source->constantField(Object, Frontier, F.Decl.At);
      Source->constantAggregate(F.Type, *Args, F.Decl.At, nullptr, &Base);
    } else {
      auto Built = Source->construct(F.Type, *Args, F.Decl.At, Address, nullptr,
                                     Frontier < R.Bases.size());
      if (!Current.IR)
        Source->constantFieldPlace(Object, Frontier)
            .write(*Source, Built, F.Decl.At);
    }
    Source->endExpression(Mark);
    Source->Scopes = std::move(Old);
    Source->Self = Previous;
    Source->Transaction = PreviousTxn;
    if (Current.IR) {
      Current.B.SetInsertPoint(Source->B.GetInsertBlock());
      Current.finishVirtualBase(Object, Frontier);
    }
    ++Frontier;
    publish(Current);
    if (Frontier == R.Bases.size())
      enterLayer();
  }
}
void Construction::enter(Frame &Em, size_t Depth) {
  auto *D = Chain[Depth].first;
  Activations[D] = &Em;
  auto *Old = Em.Transaction;
  Em.Transaction = this;
  atEachPosition(Em, [&] { advance(Em); });
  llvm::SaveAndRestore Receiver(Em.ConstantReceiver, Em.IR ? nullptr : &Object);
  Em.constructorBody(D->Decl.Children.front());
  Em.Transaction = Old;
  Activations.erase(D);
}
void Construction::run(Frame &Root) {
  if (!Root.IR)
    Root.U.ConstantInvariantLifetimes.push_back(&Object);
  auto End = llvm::scope_exit([&] {
    if (!Root.IR)
      Root.U.ConstantInvariantLifetimes.pop_back();
  });
  enter(Root, 0);
  if (positions() != Positions{Order.size()})
    fail(Root.F->Decl.At, "incomplete construction plan");
}
void Construction::rollback(Frame &Em) const {
  if (MethodContract || !Cursor)
    return;
  // A continuing transfer can leave from a producer activation or from an
  // initializing helper. Use the published progress shared by those calls.
  const auto &R = Em.U.Records.at(Object.Type);
  unsigned First = Object.BaseView ? R.VirtualCount : 0;
  auto *Complete = Em.B.CreateLoad(Em.B.getInt32Ty(), Cursor);
  Em.B.CreateStore(Em.B.getInt32(First), Cursor);
  Em.rollbackConstructionPrefix(Object,
                                Em.B.CreateZExt(Complete, Em.B.getInt64Ty()));
}
void Construction::delegate(Frame &Em, const Node &N) {
  size_t I = 0;
  while (I < Chain.size() && Chain[I].first != Em.F)
    ++I;
  if (I + 1 >= Chain.size())
    fail(N.At, "unresolved delegation");
  auto *D = Chain[I + 1].first;
  auto Actual = Em.evaluateArguments(N.Children, D);
  Em.admitArguments(Actual, D, N.At);
  auto &Args = Actual.Values;
  Frame Next(Em.U, D, Em.IR);
  if (!Em.IR) {
    Next.bindInlineParams(Args);
    Next.checkContracts(true);
    enter(Next, I + 1);
    Em.HasDelegated = true;
    return;
  }
  auto *Before = Em.wholeEpoch();
  Next.B.SetInsertPoint(Em.B.GetInsertBlock());
  Next.BaseLayer = Em.BaseLayer;
  Next.Self = Object;
  Next.Scopes[0].Names["this"] = {Object.Type + "*", Object.Address};
  Next.bindInlineParams(Args);
  Next.checkContracts(true);
  Next.InlineReturn = Em.block("delegate.done");
  enter(Next, I + 1);
  if (Next.Live) {
    Next.checkContracts(false);
    Next.cleanup(0);
  }
  Next.branch(Next.InlineReturn);
  Em.B.SetInsertPoint(Next.InlineReturn);
  Em.propagateWhole(Before);
  Em.HasDelegated = true;
}

// A method's public entry contract supplies the minimum guaranteed live prefix.
// The containing constructor owns the remaining producers, including those
// originating in a construction tail or in a suspended delegating activation.
Construction::Construction(Frame &Em, Function &Method)
    : Object(Em.Self), TailFrame(nullptr), MethodContract(&Method) {
  for (const auto &F : Em.U.Records.at(Object.Type).Fields)
    Order.push_back(F.Decl.Text);
  Chain.emplace_back(&Method, nullptr);
  findReservations(Em);
  if (!Method.Initializes.empty()) {
    Frontier = *Method.Initializes.begin();
    Cursor = Em.allocate("i32", Method.Decl.At);
    publish(Em);
  } else if (!Method.RequiresAlive.empty())
    Frontier = *Method.RequiresAlive.rbegin() + 1;
}

void Construction::checkReturn(const Token &At) const {
  if (MethodContract && !MethodContract->Initializes.empty() &&
      *positions().begin() <= *MethodContract->Initializes.rbegin())
    fail(At, "LIFE001: initializes postcondition is not established on normal "
             "return");
}

static llvm::StructType *hookType(Frame &Em) {
  auto *Ptr = Em.B.getPtrTy();
  return llvm::StructType::get(Em.U.C, {Ptr, Ptr});
}

void Construction::finishSlot(Frame &Em) {
  if (!MethodContract) {
    ++Frontier;
    publish(Em);
    advance(Em);
    return;
  }
  const auto &Outputs = MethodContract->Initializes;
  auto It = Outputs.find(Frontier);
  assert(It != Outputs.end());
  auto *Hooks = MethodContract->IR->getArg(MethodContract->IR->arg_size() - 1);
  auto *Type = hookType(Em);
  auto *Entry = Em.B.CreateGEP(
      Type, Hooks, Em.B.getInt64(std::distance(Outputs.begin(), It)));
  auto get = [&](unsigned I) {
    return Em.B.CreateLoad(Em.B.getPtrTy(),
                           Em.B.CreateStructGEP(Type, Entry, I));
  };
  auto *Before = Em.wholeEpoch();
  Em.B.CreateCall(
      llvm::FunctionType::get(Em.B.getVoidTy(), {Em.B.getPtrTy()}, false),
      get(0), {get(1)});
  Em.propagateWhole(Before);
  ++Frontier;
  if (++It != Outputs.end())
    Frontier = *It;
  publish(Em);
}

// Emit the caller's deferred producers in a native continuation. Its captured
// values refer to the live activation supplying each producer. The helper calls
// it immediately after constructing that slot, before its next source
// statement.
std::pair<llvm::Function *, llvm::Value *>
Construction::slotCallback(Frame &Em, unsigned Slot) {
  auto *FT =
      llvm::FunctionType::get(Em.B.getVoidTy(), {Em.B.getPtrTy()}, false);
  auto *Hook = llvm::Function::Create(FT, llvm::GlobalValue::InternalLinkage,
                                      "cpn.initializes." + Order[Slot], Em.U.M);
  std::set<Frame *> Frames{&Em};
  if (TailFrame)
    Frames.insert(TailFrame);
  for (auto &[Owner, F] : Activations)
    Frames.insert(F);
  struct SavedFrame {
    Frame *F;
    llvm::Function *IR;
    llvm::IRBuilderBase::InsertPoint IP;
    llvm::BasicBlock *Return;
    std::vector<Value> Temps;
    std::vector<Local> Scopes;
  };
  std::vector<SavedFrame> Saved;
  for (auto *F : Frames) {
    Saved.push_back({F, F->IR, F->B.saveIP(), F->InlineReturn,
                     std::move(F->Temps), F->Scopes});
    F->Temps.clear();
    for (auto &Scope : F->Scopes)
      Scope.Drops.clear();
    F->InlineReturn = nullptr;
    F->IR = Hook;
  }
  Em.B.SetInsertPoint(Em.block("entry"));
  finishSlot(Em);
  Em.B.CreateRetVoid();
  for (auto &S : Saved) {
    S.F->IR = S.IR;
    S.F->InlineReturn = S.Return;
    S.F->Temps = std::move(S.Temps);
    S.F->Scopes = std::move(S.Scopes);
    S.F->B.restoreIP(S.IP);
  }

  llvm::SetVector<llvm::Value *> Inputs;
  auto captured = [&](llvm::Value *V) {
    if (auto *I = llvm::dyn_cast<llvm::Instruction>(V))
      return I->getFunction() != Hook;
    if (auto *A = llvm::dyn_cast<llvm::Argument>(V))
      return A->getParent() != Hook;
    return false;
  };
  for (auto &Block : *Hook)
    for (auto &I : Block)
      for (auto &U : I.operands())
        if (captured(U.get()))
          Inputs.insert(U.get());
  if (Inputs.empty())
    return {Hook, llvm::ConstantPointerNull::get(Em.B.getPtrTy())};
  std::vector<llvm::Type *> Types;
  for (auto *V : Inputs)
    Types.push_back(V->getType());
  auto *Env = llvm::StructType::get(Em.U.C, Types);
  llvm::IRBuilder<> Allocate(Em.IR->getEntryBlock().begin());
  auto *Capture = Allocate.CreateAlloca(Env, nullptr, "construction.context");
  llvm::IRBuilder<> Entry(&*Hook->getEntryBlock().begin());
  for (size_t I = 0; I < Inputs.size(); ++I) {
    auto *V = Inputs[I];
    Em.B.CreateStore(V, Em.B.CreateStructGEP(Env, Capture, I));
    auto *Local = Entry.CreateLoad(
        Types[I], Entry.CreateStructGEP(Env, Hook->getArg(0), I));
    V->replaceUsesWithIf(Local, [&](llvm::Use &U) {
      auto *User = llvm::dyn_cast<llvm::Instruction>(U.getUser());
      return User && User->getFunction() == Hook;
    });
  }
  return {Hook, Capture};
}

bool Construction::mayAccess(const EffectBound &Effects,
                             const EffectSet &Predicate,
                             llvm::StringRef Region) {
  auto Matches = [&](const EffectSet &Bound) {
    return Bound.count(("read:" + Region).str()) ||
           Bound.count(("write:" + Region).str()) || Bound.count("read:any") ||
           Bound.count("write:any") || Bound.count("foreign") ||
           Bound.count("whole");
  };
  return !Effects || Matches(*Effects) || Matches(Predicate);
}

void Construction::checkCallArguments(Frame &Em, llvm::ArrayRef<Value> Actual,
                                      llvm::ArrayRef<std::string> Params,
                                      const EffectBound &Effects,
                                      const EffectSet &Predicate,
                                      const Token &At) const {
  if (Em.TypeQuery)
    return;
  for (auto [Index, Argument] : llvm::enumerate(Actual)) {
    llvm::StringRef Parameter = Params[Index];
    llvm::Value *Designated = Parameter.ends_with("*")   ? Argument.IR
                              : Parameter.ends_with("&") ? Argument.Address
                                                         : nullptr;
    if (!Designated)
      continue;
    const bool Layer = Designated == Object.Address &&
                       (Argument.Type == Object.Type ||
                        (Parameter.ends_with("*") &&
                         unconst(element(Argument.Type)) == Object.Type));
    const bool Base = Argument.ConstructionBase &&
                      Argument.ConstructionBase->first == Object.Address;
    if (!Layer && !Base)
      continue;
    if (!mayAccess(Effects, Predicate, "#" + std::to_string(Index)))
      continue;
    if (Base)
      checkBaseAccess(Em, Argument, At);
    else if (!Order.empty()) {
      auto Last = At;
      Last.Text = Order.back();
      checkAccess(Em, Last);
    }
  }
}

llvm::Value *Construction::admitCall(Frame &Em, const Function &D,
                                     const Token &At) {
  if (D.Owner != Object.Type) {
    if (!D.Initializes.empty())
      fail(At,
           "LIFE001: initializes requires Pending slots in the receiver layer");
    return nullptr;
  }
  for (auto I : D.RequiresAlive) {
    auto T = At;
    T.Text = Order[I];
    checkAccess(Em, T);
  }
  if (D.Initializes.empty()) {
    if (D.RequiresAlive.empty() && !Order.empty() &&
        mayAccess(D.Effects, D.PredicateEffects, "this")) {
      auto Last = At;
      Last.Text = Order.back();
      checkAccess(Em, Last);
    }
    return nullptr;
  }
  auto States = positions();
  unsigned First = *D.Initializes.begin();
  if (!States.count(First))
    fail(At, "LIFE001: initializes requires Pending slots at the "
             "initialization frontier");
  if (States.size() != 1) {
    Em.Opt.diagnose(At, Severity::Anomaly, "LIFE003",
                    "initializes entry depends on the incoming path");
    Em.guard(Em.B.CreateICmpNE(Em.B.CreateLoad(Em.B.getInt32Ty(), Cursor),
                               Em.B.getInt32(First)));
  }
  restore({First});
  auto *Type = hookType(Em);
  llvm::IRBuilder<> Allocate(Em.IR->getEntryBlock().begin());
  auto *Hooks = Allocate.CreateAlloca(Type, Em.B.getInt32(D.Initializes.size()),
                                      "construction.hooks");
  unsigned J = 0;
  for (auto I : D.Initializes) {
    if (Frontier != I || !Reserved.count(Order[I]))
      fail(At, "LIFE001: initializes slot '" + Order[I] +
                   "' is not reserved at the frontier");
    auto [Callback, Environment] = slotCallback(Em, I);
    auto *Entry = Em.B.CreateGEP(Type, Hooks, Em.B.getInt32(J++));
    Em.B.CreateStore(Callback, Em.B.CreateStructGEP(Type, Entry, 0));
    Em.B.CreateStore(Environment, Em.B.CreateStructGEP(Type, Entry, 1));
  }
  return Hooks;
}
