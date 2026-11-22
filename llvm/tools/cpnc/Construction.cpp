#include "Sema.h"
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
  if (Em.BaseLayer)
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
  if (!Reserved.empty()) {
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
  if (Frontier == R.Bases.size())
    Current.installTables(Object);
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
    Source->B.SetInsertPoint(Current.B.GetInsertBlock());
    auto *Address = Source->fieldAddress(Object, Frontier);
    auto Previous = Source->Self;
    auto *PreviousTxn = Source->Transaction;
    Source->Transaction = this;
    Source->Self = Object;
    Local Earlier;
    Earlier.Names["this"] = {Object.Type + "*", Object.Address};
    for (size_t I = 0; I < R.Fields.size(); ++I) {
      auto &Member = R.Fields[I];
      Earlier.Names[Member.Decl.Text] =
          I >= Frontier
              ? Value{}
              : Value{Member.Type, nullptr, Source->fieldAddress(Object, I)};
    }
    // Constructor parameters shadow members. Body-local declarations never
    // participate in the declarative initializer environment.
    auto Old = std::move(Source->Scopes);
    if (It != Explicit.end() && !It->second.Owner) {
      Source->Scopes = Old;
      Source->Scopes.push_back(std::move(Earlier));
    } else {
      Source->Scopes = {std::move(Earlier), Old.front()};
    }
    Source->construct(F.Type, *Args, F.Decl.At, Address, nullptr,
                      Frontier < R.Bases.size());
    Source->endExpression();
    Source->Scopes = std::move(Old);
    Source->Self = Previous;
    Source->Transaction = PreviousTxn;
    Current.B.SetInsertPoint(Source->B.GetInsertBlock());
    ++Frontier;
    publish(Current);
    if (Frontier == R.Bases.size())
      Current.installTables(Object);
  }
}
void Construction::enter(Frame &Em, size_t Depth) {
  auto *D = Chain[Depth].first;
  Activations[D] = &Em;
  auto *Old = Em.Transaction;
  Em.Transaction = this;
  atEachPosition(Em, [&] { advance(Em); });
  Em.stmt(D->Decl.Children.front());
  Em.Transaction = Old;
  Activations.erase(D);
}
void Construction::run(Frame &Root) {
  enter(Root, 0);
  if (positions() != Positions{Order.size()})
    fail(Root.F->Decl.At, "incomplete construction plan");
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
  Next.B.SetInsertPoint(Em.B.GetInsertBlock());
  Next.BaseLayer = Em.BaseLayer;
  Next.Self = Object;
  Next.Scopes[0].Names["this"] = {Object.Type + "*", Object.Address};
  Next.bindInlineParams(Args);
  Next.InlineReturn = Em.block("delegate.done");
  enter(Next, I + 1);
  if (Next.Live)
    Next.cleanup(0);
  Next.branch(Next.InlineReturn);
  Em.B.SetInsertPoint(Next.InlineReturn);
  Em.HasDelegated = true;
}
