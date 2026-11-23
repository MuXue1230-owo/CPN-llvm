#include "Sema.h"
using namespace cpn;
namespace {
// For each path, only the first use of a slot affects its eligibility. Joining
// the three possible histories keeps the analysis finite even at a loop edge.
enum History : unsigned { Unseen = 1, Read = 2, Written = 4 };
using Names = std::set<std::string>;
struct Flow {
  unsigned Next = 0, Return = 0, Break = 0, Continue = 0;
};
Flow merge(Flow A, Flow B) {
  return {A.Next | B.Next, A.Return | B.Return, A.Break | B.Break,
          A.Continue | B.Continue};
}
unsigned observe(unsigned State, History H) {
  return (State & ~Unseen) | ((State & Unseen) ? unsigned(H) : 0);
}
struct ReceiverView {
  bool Pointer, Readonly;
  bool operator==(const ReceiverView &Other) const {
    return Pointer == Other.Pointer && Readonly == Other.Readonly;
  }
};
using Views = std::map<std::string, ReceiverView>;

std::optional<ReceiverView> receiverView(const Node &N, const Views &Aliases) {
  if (N.K == Node::Name) {
    if (auto I = Aliases.find(N.Text); I != Aliases.end())
      return I->second;
  } else if (N.K == Node::Configured) {
    return receiverView(N.Children.front(), Aliases);
  } else if (N.K == Node::Conditional) {
    auto Left = receiverView(N.Children[1], Aliases);
    auto Right = receiverView(N.Children[2], Aliases);
    if (Left == Right)
      return Left;
  } else if (N.K == Node::Unary && (N.Text == "&" || N.Text == "*")) {
    auto Inner = receiverView(N.Children.front(), Aliases);
    bool Address = N.Text == "&";
    if (Inner && Inner->Pointer != Address)
      return ReceiverView{Address, Inner->Readonly};
  }
  return std::nullopt;
}

std::optional<ReceiverView> memberView(const Node &N, const Views &Aliases) {
  if (N.K == Node::Member) {
    auto View = receiverView(N.Children.front(), Aliases);
    if (View && View->Pointer == N.Definition)
      return View;
  }
  return std::nullopt;
}
bool field(const Node &N, const std::string &Slot, const Names &Locals,
           const Views &Aliases) {
  if (N.K == Node::Name)
    return N.Text == Slot && !Locals.count(Slot);
  return N.Text == Slot && memberView(N, Aliases).has_value();
}
struct SourceAnalysis {
  Frame &Em;
  const std::string &Slot;
  const std::vector<std::pair<Function *, const Node *>> &Chain;
  std::map<const Node *, Function *> &Selected;
  std::map<SourcePosition, unsigned> Entry, Exit;
  std::map<std::string, unsigned> Labels, Breaks, Continues;
  Function *Owner = nullptr;
  std::vector<const Node *> Declarations;
  Views ReceiverAliases;
  SourceAnalysis(Frame &Em, const std::string &Slot,
                 const std::vector<std::pair<Function *, const Node *>> &Chain,
                 std::map<const Node *, Function *> &Selected)
      : Em(Em), Slot(Slot), Chain(Chain), Selected(Selected) {}
  Function *method(const Node &Call, const Names &Locals) {
    const auto &Callee = Call.Children.front();
    bool Self = Callee.K == Node::Name && !Locals.count(Callee.Text);
    auto View = memberView(Callee, ReceiverAliases);
    if (!Self && !View)
      return nullptr;
    auto Key = Owner->Owner + "::" + Callee.Text;
    auto I = Em.U.Overloads.find(Key);
    bool Families = Em.U.FunctionFamilies.count(Key);
    if (I == Em.U.Overloads.end() && !Families)
      return nullptr;
    if (auto Cached = Selected.find(&Call); Cached != Selected.end())
      return Cached->second;
    auto *D = I == Em.U.Overloads.end() ? nullptr : I->second.front();
    if (Families ||
        (I->second.size() > 1 && llvm::any_of(I->second, [&](auto *Other) {
           return D->Initializes != Other->Initializes ||
                  D->RequiresAlive != Other->RequiresAlive ||
                  D->Effects != Other->Effects ||
                  D->PredicateEffects != Other->PredicateEffects;
         }))) {
      auto *FT = llvm::FunctionType::get(Em.B.getVoidTy(), false);
      auto *Tmp = llvm::Function::Create(FT, llvm::GlobalValue::InternalLinkage,
                                         "cpn.contract.lookup", Em.U.M);
      Function Query = *Owner;
      Frame Probe(Em.U, &Query, Tmp);
      Probe.TypeQuery = true;
      Probe.B.SetInsertPoint(Probe.block("entry"));
      Probe.Self = {Owner->Owner, nullptr,
                    Probe.allocate(Owner->Owner, Call.At)};
      Probe.Scopes[0].Names["this"] = {Owner->Owner + "*", Probe.Self.Address};
      auto local = [&](const Node &N, std::string T) {
        if (llvm::StringRef(T).ends_with("&"))
          T.resize(T.find_last_not_of('&') + 1);
        auto Mutable = unconst(T);
        Probe.Scopes[0].Names[N.Text] = {Mutable, nullptr,
                                         Probe.allocate(Mutable, N.At),
                                         N.Const || T != Mutable};
      };
      for (unsigned J = 0; J < Owner->Params.size(); ++J)
        local(Owner->Decl.Params[J], Owner->Params[J]);
      for (auto *N : Declarations)
        if (N->K == Node::Alias)
          Probe.Scopes[0].Aliases[N->Text] = Probe.resolve(N->Type, N->At);
        else if (N->K == Node::Object)
          local(*N, N->Type == "auto"
                        ? Probe.unevaluatedType(N->Children.front(), false)
                        : Probe.resolve(N->Type, N->At));
      std::vector<Value> Actual;
      for (const auto &Arg : llvm::ArrayRef(Call.Children).drop_front())
        Actual.push_back(Probe.eval(Arg));
      auto Receiver = Probe.Self;
      Receiver.Readonly = View ? View->Readonly : Owner->Decl.Const;
      D = Probe.select(Callee.Text, Callee, Actual, Receiver);
      Tmp->eraseFromParent();
    }
    Selected[&Call] = D;
    return D;
  }
  unsigned addressExpression(const Node &N, unsigned S, const Names &Locals) {
    // The receiver designation itself does not read a field. Any expression
    // selecting it still executes in source order before the read or write.
    if (N.K == Node::Conditional) {
      S = expression(N.Children[0], S, Locals);
      return addressExpression(N.Children[1], S, Locals) |
             addressExpression(N.Children[2], S, Locals);
    }
    if (N.K == Node::Member || N.K == Node::Unary || N.K == Node::Configured)
      return addressExpression(N.Children.front(), S, Locals);
    return S;
  }
  unsigned callArguments(const Node &Call, unsigned S, const Names &Locals,
                         llvm::ArrayRef<std::string> Params,
                         const EffectBound &Effects,
                         const EffectSet &Predicate) {
    for (auto [I, Arg] :
         llvm::enumerate(llvm::ArrayRef(Call.Children).drop_front())) {
      llvm::StringRef Type =
          I < Params.size() ? llvm::StringRef(Params[I]) : llvm::StringRef();
      auto View = receiverView(Arg, ReceiverAliases);
      // Binding a borrow with a closed non-accessing region does not read
      // the selected slot. Binding an aggregate value can still copy it.
      bool Borrow = View && (Type.ends_with("&") ||
                             (View->Pointer && Type.ends_with("*")));
      if (Borrow &&
          !Construction::mayAccess(Effects, Predicate, "#" + std::to_string(I)))
        S = addressExpression(Arg, S, Locals);
      else
        S = expression(Arg, S, Locals);
    }
    return S;
  }
  Function *freeFunction(const Node &Callee, const Names &Locals) {
    if (Callee.K != Node::Name || Locals.count(Callee.Text) ||
        Callee.ExplicitApplication)
      return nullptr;
    Frame Bind(Em.U, Owner, nullptr);
    if (Bind.typeCallee(Callee.Text, Callee.At) ||
        !Bind.methodOwner(Owner->Owner, Callee.At).empty())
      return nullptr;
    auto Key = Bind.callKey(Callee.Text);
    if (Em.U.FunctionFamilies.count(Key))
      return nullptr;
    auto Candidates = Bind.visibleOverloads(Key);
    if (Candidates.size() != 1 || !Candidates.front()->Owner.empty())
      return nullptr;
    return Candidates.front();
  }
  std::string declaredType(const Node &N) {
    Frame Types(Em.U, Owner, nullptr);
    for (auto *Decl : Declarations) {
      // Local nominal definitions have not been bound by the emitter yet.
      if (Decl->K == Node::Record || Decl->K == Node::Union ||
          Decl->K == Node::Enumeration)
        return {};
      if (Decl->K == Node::Alias)
        Types.Scopes.back().Aliases[Decl->Text] =
            Types.resolve(Decl->Type, Decl->At);
    }
    return Types.resolve(N.Type, N.At);
  }
  std::string indirectSignature(const Node &Name, const Names &Locals) {
    if (Name.K != Node::Name || !Locals.count(Name.Text) ||
        Name.ExplicitApplication)
      return {};
    auto Signature = [&](std::string Type) {
      if (llvm::StringRef(Type).ends_with("&"))
        Type.resize(Type.find_last_not_of('&') + 1);
      Type = unconst(Type);
      if (llvm::StringRef(Type).ends_with("*") &&
          Em.U.Signatures.count(element(Type)))
        return element(Type);
      return std::string();
    };
    for (auto *D : llvm::reverse(Declarations))
      if (D->Text == Name.Text)
        return {};
    for (auto [I, Param] : llvm::enumerate(Owner->Decl.Params))
      if (Param.Text == Name.Text)
        return Signature(Owner->Params[I]);
    return {};
  }
  std::optional<ReceiverView> aliasBinding(const Node &N) {
    if (!Em.IR || N.Children.size() != 1 || N.Settings.count("storage"))
      return std::nullopt;
    auto View = receiverView(N.Children.front(), ReceiverAliases);
    if (!View)
      return std::nullopt;
    if (N.Type == "auto")
      return N.Const && View->Pointer ? View : std::nullopt;
    auto T = declaredType(N);
    auto Object = unconst(T);
    if (View->Pointer) {
      if ((!N.Const && Object == T) || !llvm::StringRef(Object).ends_with("*"))
        return std::nullopt;
      Object = element(Object);
    } else {
      if (!llvm::StringRef(Object).ends_with("&"))
        return std::nullopt;
      Object.resize(Object.find_last_not_of('&') + 1);
    }
    if (unconst(Object) != Owner->Owner)
      return std::nullopt;
    View->Readonly |= Object != unconst(Object) || (!View->Pointer && N.Const);
    return View;
  }
  unsigned expression(const Node &N, unsigned S, const Names &Locals) {
    if (!S)
      return 0;
    if (N.K == Node::Unary && (N.Text == "sizeof" || N.Text == "alignof"))
      return S;
    if (N.K == Node::Lambda) {
      for (const auto &Capture : N.TemplateArgs) {
        if (Capture.Type == "initializer")
          S = expression(Capture.Children.front(), S, Locals);
        else if (Capture.Type != "this" && Capture.Text == Slot &&
                 !Locals.count(Slot))
          S = observe(S, Read);
      }
      return S;
    }
    if (field(N, Slot, Locals, ReceiverAliases) ||
        receiverView(N, ReceiverAliases))
      return observe(addressExpression(N, S, Locals), Read);
    if (N.K == Node::Binary && N.Text == "=" &&
        field(N.Children[0], Slot, Locals, ReceiverAliases)) {
      S = addressExpression(N.Children[0], S, Locals);
      return observe(expression(N.Children[1], S, Locals), Written);
    }
    // A qualified access to a different immediate member does not read this
    // slot. Passing this to an opaque call, however, exposes the whole layer.
    if (memberView(N, ReceiverAliases))
      return addressExpression(N, S, Locals);
    if (N.K == Node::Conditional) {
      S = expression(N.Children[0], S, Locals);
      return expression(N.Children[1], S, Locals) |
             expression(N.Children[2], S, Locals);
    }
    if (N.K == Node::Binary && (N.Text == "&&" || N.Text == "||")) {
      S = expression(N.Children[0], S, Locals);
      return S | expression(N.Children[1], S, Locals);
    }
    if (N.K == Node::Call) {
      if (auto *D = method(N, Locals)) {
        S = addressExpression(N.Children.front(), S, Locals);
        S = callArguments(N, S, Locals, D->Params, D->Effects,
                          D->PredicateEffects);
        const auto &Fields = Em.U.Records.at(D->Owner).Fields;
        for (auto I : D->Initializes)
          if (Fields[I].Decl.Text == Slot)
            return observe(S, Written);
        for (auto I : D->RequiresAlive)
          if (Fields[I].Decl.Text == Slot)
            return observe(S, Read);
        return D->Initializes.empty() && D->RequiresAlive.empty() &&
                       Construction::mayAccess(D->Effects, D->PredicateEffects,
                                               "this")
                   ? observe(S, Read)
                   : S;
      }
      const auto &Callee = N.Children.front();
      if (auto *D = freeFunction(Callee, Locals))
        return callArguments(N, S, Locals, D->Params, D->Effects,
                             D->PredicateEffects);
      if (auto Sig = indirectSignature(Callee, Locals); !Sig.empty())
        return callArguments(
            N, S, Locals, llvm::ArrayRef(Em.U.Signatures.at(Sig)).drop_front(),
            callableEffects(Sig), callablePredicateEffects(Sig));
    }
    for (auto &C : N.Children)
      S = expression(C, S, Locals);
    return S;
  }
  unsigned activation(size_t Depth, unsigned S) {
    auto *D = Chain[Depth].first;
    llvm::SaveAndRestore Current(Owner, D);
    llvm::SaveAndRestore Environment(Declarations);
    llvm::SaveAndRestore Aliases(ReceiverAliases,
                                 Views{{"this", {true, D->Decl.Const}}});
    Declarations.clear();
    // Gotos form ordinary CFG edges, including back edges and jumps into
    // another lexical block admitted by the binding pass. Each destination
    // can gain at most three first-use histories during fixed-point iteration.
    llvm::SaveAndRestore SaveLabels(Labels), SaveBreaks(Breaks),
        SaveContinues(Continues);
    Labels.clear();
    Breaks.clear();
    Continues.clear();
    for (;;) {
      auto Previous = Labels;
      Names Locals;
      for (auto &P : D->Decl.Params)
        Locals.insert(P.Text);
      auto End = statement(D->Decl.Children.front(), S, Locals, Depth);
      if (Labels == Previous)
        return End.Next | End.Return;
    }
  }
  Flow statement(const Node &N, unsigned S, Names &Locals, size_t Depth,
                 const std::string &Label = "") {
    if (N.K == Node::Label)
      S |= Labels[N.Text];
    SourcePosition P{N.At.Line, N.At.Column};
    if (N.K == Node::Block || N.K == Node::Label)
      Entry[P] |= S;
    auto F = traverse(N, S, Locals, Depth, Label);
    if (N.K == Node::For || N.K == Node::While || N.K == Node::Do ||
        N.K == Node::Switch || N.K == Node::Match)
      Exit[P] |= F.Next;
    return F;
  }
  Flow traverse(const Node &N, unsigned S, Names &Locals, size_t Depth,
                const std::string &Label) {
    auto &A = N.Children;
    switch (N.K) {
    case Node::Block: {
      llvm::SaveAndRestore Environment(Declarations);
      llvm::SaveAndRestore Aliases(ReceiverAliases);
      Names Scope = Locals;
      Flow Out{S};
      for (auto &C : A) {
        auto R = statement(C, Out.Next, Scope, Depth);
        Out.Next = 0;
        Out = merge(Out, R);
      }
      return Out;
    }
    case Node::Record:
    case Node::Enumeration:
    case Node::Union:
      Declarations.push_back(&N);
      Locals.insert(N.Text);
      ReceiverAliases.erase(N.Text);
      return {S};
    case Node::Init:
      return {S};
    case Node::Alias:
      Declarations.push_back(&N);
      Locals.insert(N.Text);
      ReceiverAliases.erase(N.Text);
      return {S};
    case Node::Object: {
      auto View = aliasBinding(N);
      unsigned Next = View ? addressExpression(N.Children.front(), S, Locals)
                           : expression(N, S, Locals);
      Declarations.push_back(&N);
      Locals.insert(N.Text);
      ReceiverAliases.erase(N.Text);
      if (View)
        ReceiverAliases.emplace(N.Text, *View);
      return {Next};
    }
    case Node::Delegate:
      for (auto &C : A)
        S = expression(C, S, Locals);
      return {Depth + 1 < Chain.size() ? activation(Depth + 1, S) : S};
    case Node::If: {
      S = expression(A[0], S, Locals);
      if (N.Required) {
        auto V = Em.constantEval(A[0]);
        auto *Cond = llvm::dyn_cast<llvm::ConstantInt>(V.IR);
        if (Cond) {
          if (!Cond->isZero())
            return statement(A[1], S, Locals, Depth);
          return A.size() > 2 ? statement(A[2], S, Locals, Depth) : Flow{S};
        }
      }
      auto Y = statement(A[1], S, Locals, Depth);
      return merge(Y,
                   A.size() > 2 ? statement(A[2], S, Locals, Depth) : Flow{S});
    }
    case Node::Return:
      return {0, expression(N, S, Locals)};
    case Node::Break:
    case Node::Continue:
      if (!N.Text.empty()) {
        (N.K == Node::Break ? Breaks : Continues)[N.Text] |= S;
        return {};
      }
      return N.K == Node::Break ? Flow{0, 0, S, 0} : Flow{0, 0, 0, S};
    case Node::For:
    case Node::While:
    case Node::Do: {
      llvm::SaveAndRestore Environment(Declarations);
      llvm::SaveAndRestore Aliases(ReceiverAliases);
      bool For = N.K == Node::For, Do = N.K == Node::Do;
      Names Scope = Locals;
      if (For)
        S = statement(A[0], S, Scope, Depth).Next;
      unsigned Header = S, Previous;
      Flow Out;
      do {
        Previous = Header;
        auto &Test = A[For || Do ? 1 : 0];
        if (!Do)
          Entry[{Test.At.Line, Test.At.Column}] |= Header;
        unsigned BodyEntry = Do ? Header : expression(Test, Header, Scope);
        auto R = statement(A[For ? 3 : Do ? 0 : 1], BodyEntry, Scope, Depth);
        unsigned Back = R.Next | R.Continue | Continues[Label];
        if (For && A[2].K != Node::Empty) {
          Entry[{A[2].At.Line, A[2].At.Column}] |= Back;
          Back = expression(A[2], Back, Scope);
        }
        if (Do) {
          Entry[{Test.At.Line, Test.At.Column}] |= Back;
          Back = expression(Test, Back, Scope);
        }
        if (Test.K != Node::Empty &&
            !(Test.K == Node::Name && Test.Text == "true"))
          Out.Next |= Do ? Back : BodyEntry;
        Out.Next |= R.Break | Breaks[Label];
        Out.Return |= R.Return;
        Header |= Back;
      } while (Header != Previous);
      return Out;
    }
    case Node::Configured:
      return statement(A[0], S, Locals, Depth);
    case Node::Label:
      return statement(A[0], S, Locals, Depth, N.Text);
    case Node::Goto:
      Labels[N.Text] |= S;
      return {};
    case Node::Switch:
    case Node::Match: {
      bool Switch = N.K == Node::Switch, Default = false;
      unsigned Input = expression(A[0], S, Locals), Fall = 0;
      Flow Out;
      for (const auto &Arm : llvm::ArrayRef(A).drop_front()) {
        Names Scope = Locals;
        llvm::SaveAndRestore Bindings(Declarations);
        llvm::SaveAndRestore Aliases(ReceiverAliases);
        std::vector<Node> Payload;
        if (!Switch && !Arm.Params.empty()) {
          const Case *Variant = Em.findCase(Arm.Text, Arm.At);
          if (!Variant || Variant->Types.size() != Arm.Params.size())
            fail(Arm.At, "unknown case or incomplete payload pattern");
          Payload.reserve(Arm.Params.size());
          for (size_t J = 0; J < Arm.Params.size(); ++J) {
            auto &P = Arm.Params[J];
            if (P.Type == "_")
              continue;
            auto &V = Payload.emplace_back(Node::Object, P.At);
            V.Text = P.Text;
            V.Type = Variant->Types[J];
            V.Const = P.Type == "ref" && Variant->Decl.Params[J].Const;
            Scope.insert(P.Text);
            ReceiverAliases.erase(P.Text);
            Declarations.push_back(&V);
          }
        }
        const auto &Body = Arm.Children.back();
        auto R = statement(Body, Input | Fall, Scope, Depth);
        bool Falls = Switch && !Body.Children.empty() &&
                     Body.Children.back().K == Node::Fallthrough;
        Fall = Falls ? R.Next : 0;
        Out.Next |= Falls ? 0 : R.Next;
        if (Switch)
          Out.Next |= R.Break | Breaks[Label];
        else
          Out.Break |= R.Break;
        Out.Continue |= R.Continue;
        Out.Return |= R.Return;
        Default |= Arm.Children.size() == 1;
      }
      if (Switch && !Default)
        Out.Next |= Input;
      return Out;
    }
    default:
      return {expression(N, S, Locals)};
    }
  }
};
} // namespace
void Construction::findReservations(Frame &Em) {
  std::map<const Node *, Function *> Selected;
  for (size_t I = 0; I < Order.size(); ++I) {
    const auto &Field = Em.U.Records.at(Object.Type).Fields[I];
    auto &Name = Order[I];
    if (MethodContract ? !MethodContract->Initializes.count(I)
                       : Field.Decl.K != Node::Field ||
                             Field.Decl.HasInitializer || Explicit.count(Name))
      continue;
    SourceAnalysis Analysis(Em, Name, Chain, Selected);
    auto End = Analysis.activation(0, Unseen);
    if (MethodContract && (End & Read))
      fail(MethodContract->Decl.At,
           "LIFE002: use before initialization of '" + Name + "'");
    if (MethodContract && (End & Unseen))
      fail(MethodContract->Decl.At, "LIFE001: initializes postcondition is not "
                                    "established on normal return");
    if (End != Written && !MethodContract)
      continue;
    Reserved.insert(Name);
    for (auto &[P, States] : Analysis.Entry)
      Entries[P][I] = States;
    for (auto &[P, States] : Analysis.Exit)
      Exits[P][I] = States;
  }
}
Construction::Positions Construction::positions() const {
  return Alternatives.empty() ? Positions{Frontier} : Alternatives;
}
void Construction::restore(const Positions &P) {
  assert(!P.empty());
  Frontier = *P.begin();
  Alternatives = P.size() == 1 ? Positions{} : P;
}
void Construction::publish(Frame &Em) {
  if (Cursor)
    Em.B.CreateStore(Em.B.getInt32(Frontier), Cursor);
}
void Construction::checkAccess(Frame &Em, const Token &T) const {
  auto I = std::find(Order.begin(), Order.end(), T.Text);
  if (I == Order.end())
    return;
  size_t Slot = I - Order.begin();
  auto States = positions();
  if (*States.rbegin() <= Slot)
    fail(T, "LIFE002: use before initialization");
  if (*States.begin() <= Slot) {
    Em.Opt.diagnose(T, Severity::Anomaly, "LIFE003",
                    "slot lifetime depends on the incoming path");
    if (Em.Opt.RawValidation)
      Em.guard(Em.B.CreateICmpULE(Em.B.CreateLoad(Em.B.getInt32Ty(), Cursor),
                                  Em.B.getInt32(Slot)),
               "lifecycle");
  }
}
void Construction::checkBaseAccess(Frame &Em, const Value &View,
                                   const Token &At) const {
  if (!View.ConstructionBase || View.ConstructionBase->first != Object.Address)
    return;
  auto Base = At;
  Base.Text = Order[View.ConstructionBase->second];
  checkAccess(Em, Base);
}
void Construction::atEachPosition(Frame &Em,
                                  const std::function<void()> &Action) {
  auto States = positions();
  if (States.size() == 1) {
    Action();
    return;
  }
  auto *Bad = Em.block("ctor.invalid"), *End = Em.block("ctor.merge");
  auto *Dispatch = Em.B.CreateSwitch(Em.B.CreateLoad(Em.B.getInt32Ty(), Cursor),
                                     Bad, States.size());
  Positions Result;
  for (size_t S : States) {
    auto *BB = Em.block("ctor.position");
    Dispatch->addCase(Em.B.getInt32(S), BB);
    Em.B.SetInsertPoint(BB);
    restore({S});
    Action();
    auto EndState = positions();
    Result.insert(EndState.begin(), EndState.end());
    Em.branch(End);
  }
  Em.B.SetInsertPoint(Bad);
  Em.B.CreateUnreachable();
  Em.B.SetInsertPoint(End);
  restore(Result);
}
std::optional<Value> Construction::firstWrite(Frame &Em, const Node &N) {
  if (OrdinaryAssignment == &N)
    return {};
  auto &L = N.Children[0];
  Names Locals;
  Views ReceiverAliases;
  auto Hide = [&](const std::string &Name) {
    Locals.insert(Name);
    ReceiverAliases.erase(Name);
  };
  for (auto &Scope : Em.Scopes) {
    for (const auto &[Name, V] : Scope.Names) {
      Hide(Name);
      if (Em.IR && !V.Readonly && V.Type == Object.Type &&
          V.Address == Object.Address)
        ReceiverAliases.emplace(Name, ReceiverView{false, false});
      if (Em.IR && (V.Readonly || Name == "this") &&
          V.Type == Object.Type + "*" && V.IR == Object.Address)
        ReceiverAliases.emplace(Name, ReceiverView{true, false});
    }
    for (const auto &[Name, Type] : Scope.Aliases)
      Hide(Name);
    for (const auto &Name : Scope.UnavailableNames)
      Hide(Name);
  }
  auto I = std::find_if(Reserved.begin(), Reserved.end(), [&](auto &Name) {
    return field(L, Name, Locals, ReceiverAliases);
  });
  if (I == Reserved.end())
    return {};
  size_t Index = std::find(Order.begin(), Order.end(), *I) - Order.begin();
  auto States = positions();
  if (*States.begin() > Index)
    return {};
  if (*States.rbegin() < Index)
    fail(N.At, "first assignment is beyond the initialization frontier");
  auto &R = Em.U.Records.at(Object.Type);
  auto &Type = R.Fields[Index].Type;
  if (!Em.IR) {
    auto V = Em.construct(Type, {N.Children[1]}, N.At);
    Em.constantFieldPlace(Object, Index).write(Em, V, N.At);
    finishSlot(Em);
    return V;
  }
  auto *Addr = Em.B.CreateStructGEP(R.IR, Object.Address, Index);
  atEachPosition(Em, [&] {
    if (Frontier < Index) {
      Em.guard(Em.B.getTrue());
      return;
    }
    if (Frontier > Index) {
      auto *Old = OrdinaryAssignment;
      OrdinaryAssignment = &N;
      Em.eval(N);
      OrdinaryAssignment = Old;
      return;
    }
    auto &Right = N.Children[1];
    if (Right.K == Node::Call && Right.Children[0].K == Node::Name &&
        Right.Children[0].Text == Type)
      Em.construct(Type, {Right.Children.begin() + 1, Right.Children.end()},
                   Right.At, Addr);
    else
      Em.construct(Type, {Right}, Right.At, Addr);
    finishSlot(Em);
  });
  return Em.load({Type, nullptr, Addr});
}

void Construction::restoreFlow(const Node &N, bool Exit) {
  if (Reserved.empty())
    return;
  const auto &Facts = Exit ? Exits : Entries;
  auto It = Facts.find({N.At.Line, N.At.Column});
  if (It == Facts.end())
    return;
  Positions Possible;
  size_t End =
      MethodContract ? *MethodContract->Initializes.rbegin() + 1 : Order.size();
  for (size_t I = 0; I <= End; ++I) {
    if (I < End && !Reserved.count(Order[I])) {
      auto E = Explicit.find(Order[I]);
      if (E == Explicit.end() || !E->second.Owner ||
          Activations.count(E->second.Owner))
        continue;
    }
    if (llvm::all_of(It->second, [&](const auto &Slot) {
          return Slot.second & (I > Slot.first ? Written : Unseen | Read);
        }))
      Possible.insert(I);
  }
  if (!Possible.empty())
    restore(Possible);
}
