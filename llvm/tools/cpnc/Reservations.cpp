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
bool field(const Node &N, const std::string &Slot, const Names &Locals) {
  if (N.K == Node::Name)
    return N.Text == Slot && !Locals.count(Slot);
  return N.K == Node::Member && N.Text == Slot && N.Definition &&
         N.Children.front().K == Node::Name &&
         N.Children.front().Text == "this";
}
struct SourceAnalysis {
  Frame &Em;
  const std::string &Slot;
  const std::vector<std::pair<Function *, const Node *>> &Chain;
  unsigned expression(const Node &N, unsigned S, const Names &Locals) {
    if (field(N, Slot, Locals) || (N.K == Node::Name && N.Text == "this"))
      return observe(S, Read);
    if (N.K == Node::Binary && N.Text == "=" &&
        field(N.Children[0], Slot, Locals))
      return observe(expression(N.Children[1], S, Locals), Written);
    // A qualified access to a different immediate member does not read this
    // slot. Passing this to an opaque call, however, exposes the whole layer.
    if (N.K == Node::Member && N.Definition &&
        N.Children.front().K == Node::Name && N.Children.front().Text == "this")
      return S;
    if (N.K == Node::Conditional) {
      S = expression(N.Children[0], S, Locals);
      return expression(N.Children[1], S, Locals) |
             expression(N.Children[2], S, Locals);
    }
    if (N.K == Node::Binary && (N.Text == "&&" || N.Text == "||")) {
      S = expression(N.Children[0], S, Locals);
      return S | expression(N.Children[1], S, Locals);
    }
    if (N.K == Node::Call && N.Children.front().K == Node::Name &&
        Em.U.Overloads.count(Chain.front().first->Owner +
                             "::" + N.Children.front().Text))
      S = observe(S, Read);
    for (auto &C : N.Children)
      S = expression(C, S, Locals);
    return S;
  }
  unsigned activation(size_t Depth, unsigned S) {
    auto *D = Chain[Depth].first;
    Names Locals;
    for (auto &P : D->Decl.Params)
      Locals.insert(P.Text);
    auto End = statement(D->Decl.Children.front(), S, Locals, Depth);
    return End.Next | End.Return;
  }
  Flow statement(const Node &N, unsigned S, Names &Locals, size_t Depth) {
    if (!S)
      return {};
    auto &A = N.Children;
    switch (N.K) {
    case Node::Block: {
      Names Scope = Locals;
      Flow Out{S};
      for (auto &C : A) {
        auto R = statement(C, Out.Next, Scope, Depth);
        Out.Next = 0;
        Out = merge(Out, R);
      }
      return Out;
    }
    case Node::Init:
      return {S};
    case Node::Object:
      Locals.insert(N.Text);
      return {expression(N, S, Locals)};
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
      return {0, 0, S, 0};
    case Node::Continue:
      return {0, 0, 0, S};
    case Node::For:
    case Node::While:
    case Node::Do: {
      bool For = N.K == Node::For, Do = N.K == Node::Do;
      Names Scope = Locals;
      if (For)
        S = statement(A[0], S, Scope, Depth).Next;
      unsigned Header = S, Previous = 0;
      Flow Out;
      while (Header != Previous) {
        Previous = Header;
        unsigned Entry =
            Do ? Header : expression(A[For ? 1 : 0], Header, Scope);
        auto R = statement(A[For ? 3 : Do ? 0 : 1], Entry, Scope, Depth);
        unsigned Back = R.Next | R.Continue;
        if (For)
          Back = expression(A[2], Back, Scope);
        if (Do)
          Back = expression(A[1], Back, Scope);
        Out.Next |= R.Break | (Do ? Back : Entry);
        Out.Return |= R.Return;
        Header |= Back;
      }
      return Out;
    }
    case Node::Configured:
      return statement(A[0], S, Locals, Depth);
    case Node::Label:
      return statement(A[0], S, Locals, Depth);
    // An unmodelled transfer or switch may reach a read first. It cannot
    // provide the all-path evidence needed to reserve a pending slot.
    case Node::Goto:
    case Node::Switch:
    case Node::Match:
      return {observe(S, Read)};
    default:
      return {expression(N, S, Locals)};
    }
  }
};
} // namespace
void Construction::findReservations(Frame &Em) {
  for (auto &Field : Em.U.Records.at(Object.Type).Fields) {
    auto &Name = Field.Decl.Text;
    if (Field.Decl.K != Node::Field || Field.Decl.HasInitializer ||
        Explicit.count(Name))
      continue;
    SourceAnalysis Analysis{Em, Name, Chain};
    if (Analysis.activation(0, Unseen) == Written)
      Reserved.insert(Name);
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
    fail(T, "use before initialization");
  if (*States.begin() <= Slot)
    Em.guard(Em.B.CreateICmpULE(Em.B.CreateLoad(Em.B.getInt32Ty(), Cursor),
                                Em.B.getInt32(Slot)));
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
  for (auto &Scope : Em.Scopes)
    for (auto &KV : Scope.Names)
      Locals.insert(KV.first);
  auto I = std::find_if(Reserved.begin(), Reserved.end(),
                        [&](auto &Name) { return field(L, Name, Locals); });
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
    ++Frontier;
    publish(Em);
    advance(Em);
  });
  return Em.load({Type, nullptr, Addr});
}

Construction::Positions Construction::loopPositions(const Node &Loop) const {
  auto P = positions();
  if (Reserved.empty())
    return P;
  std::function<void(const Node &)> visit = [&](const Node &N) {
    if (N.K == Node::Binary && N.Text == "=") {
      auto &Target = N.Children[0];
      if ((Target.K == Node::Name || Target.K == Node::Member) &&
          Reserved.count(Target.Text)) {
        auto I = std::find(Order.begin(), Order.end(), Target.Text);
        do {
          ++I;
        } while (I != Order.end() && !Reserved.count(*I) &&
                 (!Explicit.count(*I) || !Explicit.at(*I).Owner ||
                  Activations.count(Explicit.at(*I).Owner)));
        P.insert(I - Order.begin());
      }
    }
    for (auto &C : N.Children)
      visit(C);
  };
  visit(Loop);
  return P;
}
