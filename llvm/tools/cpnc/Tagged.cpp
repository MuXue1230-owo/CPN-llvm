#include "Sema.h"
using namespace cpn;

void Context::tagged(const Node &D, const std::string &Name,
                     const std::string &P) {
  auto &R = Records[Name];
  if (R.IR && R.Decl.K != Node::Union)
    fail(D.At, "conflicting nominal declaration");
  if (R.Complete)
    fail(D.At, "duplicate union definition");
  R.Decl = D;
  if (!R.IR)
    R.IR = llvm::StructType::create(C, "cpn." + Name);
  if (D.Prototype)
    return;
  Frame F(*this, nullptr, nullptr, P);
  std::vector<llvm::Type *> Layout{llvm::Type::getInt32Ty(C)};
  for (auto &Decl : D.Children) {
    auto Key = Name + "::" + Decl.Text;
    if (Cases.count(Key))
      fail(Decl.At, "duplicate union case");
    Case V{Name,
           unsigned(Variants[Name].size()),
           unsigned(Layout.size()),
           Decl,
           {}};
    for (auto &A : Decl.Params) {
      auto T = F.resolve(A.Type, A.At);
      auto *Ty = ir(T, A.At);
      if (!Ty->isSized())
        fail(A.At, "incomplete union payload");
      if (Records.count(T))
        fail(A.At, "nontrivial union payload is unavailable");
      V.Types.push_back(T);
      Layout.push_back(Ty);
    }
    if (Decl.Definition && !DefaultCase.emplace(Name, Key).second)
      fail(Decl.At, "duplicate default case");
    Cases[Key] = V;
    Variants[Name].push_back(Key);
  }
  R.IR->setBody(Layout);
  R.Complete = true;
}
Value Frame::variant(const Case &C, const std::vector<Node> &Args,
                     const Token &At) {
  if (Args.size() != C.Types.size())
    fail(At, "wrong union payload arity");
  auto *Ty = U.Records.at(C.Owner).IR;
  llvm::Value *V = B.CreateInsertValue(llvm::Constant::getNullValue(Ty),
                                       B.getInt32(C.Tag), 0);
  for (size_t I = 0; I < Args.size(); ++I) {
    auto A = convert(eval(Args[I]), C.Types[I], At);
    V = B.CreateInsertValue(V, A.IR, C.First + I);
  }
  return {C.Owner, V};
}
void Frame::match(const Node &N) {
  auto Subject = eval(N.Children[0]);
  if (!U.Variants.count(Subject.Type))
    fail(N.At, "match requires a union value");
  auto *Address = Subject.Address;
  if (!Address) {
    Address = allocate(Subject.Type, N.At);
    B.CreateStore(Subject.IR, Address);
  }
  auto *End = block("match.end"), *Invalid = block("match.invalid");
  auto *SW = B.CreateSwitch(B.CreateExtractValue(Subject.IR, 0), Invalid);
  std::set<std::string> Seen;
  bool Any = false, Wild = false;
  for (size_t I = 1; I < N.Children.size(); ++I) {
    auto &Arm = N.Children[I];
    auto *BB = block("match.case");
    B.SetInsertPoint(BB);
    Scopes.emplace_back();
    if (Arm.Text == "_") {
      if (Wild)
        fail(Arm.At, "duplicate wildcard");
      Wild = true;
      SW->setDefaultDest(BB);
    } else {
      auto It = U.Cases.find(Arm.Text);
      if (It == U.Cases.end() || It->second.Owner != Subject.Type)
        fail(Arm.At, "unknown union case");
      auto &C = It->second;
      if (!Seen.insert(Arm.Text).second || C.Types.size() != Arm.Params.size())
        fail(Arm.At, "duplicate case or incomplete payload pattern");
      SW->addCase(B.getInt32(C.Tag), BB);
      for (size_t J = 0; J < Arm.Params.size(); ++J) {
        auto &P = Arm.Params[J];
        if (P.Type == "_")
          continue;
        auto *Ptr = B.CreateStructGEP(U.ir(Subject.Type), Address, C.First + J);
        if (P.Type != "ref") {
          if (P.Type == "move" && !Subject.Expiring)
            fail(P.At, "move binding requires an expiring subject");
          auto *Copy = allocate(C.Types[J], P.At);
          B.CreateStore(B.CreateLoad(U.ir(C.Types[J]), Ptr), Copy);
          Ptr = Copy;
        }
        Scopes.back().Names[P.Text] = {C.Types[J], nullptr, Ptr,
                                       Subject.Readonly};
      }
    }
    Live = true;
    stmt(Arm.Children[0]);
    Any |= Live;
    branch(End);
    Scopes.pop_back();
  }
  if (!Wild && Seen.size() != U.Variants.at(Subject.Type).size())
    fail(N.At, "non-exhaustive match");
  B.SetInsertPoint(Invalid);
  B.CreateUnreachable();
  B.SetInsertPoint(End);
  Live = Any;
}
