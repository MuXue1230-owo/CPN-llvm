#include "Sema.h"
#include "llvm/Analysis/ValueTracking.h"
using namespace cpn;
llvm::Constant *Frame::symbolicAddress(Value V, const Token &At) {
  auto *Address = llvm::dyn_cast_or_null<llvm::Constant>(V.Address);
  if (!Address ||
      !llvm::isa<llvm::GlobalValue>(llvm::getUnderlyingObject(Address)))
    fail(At, "constant address must designate static storage");
  return Address;
}

Value Frame::openStaticReference(Value V) {
  if (!V.ReferenceCell)
    return V;
  if (!IR) {
    if (!V.Address)
      fail({}, "constant reference address required");
    return V;
  }
  guard(B.CreateNot(B.CreateLoad(B.getInt1Ty(), U.Ready.at(V.ReferenceCell))));
  auto *Cell = storedPointerCell(V.ReferenceCell);
  V.Address = B.CreateLoad(B.getPtrTy(), V.ReferenceCell);
  readReferent(V, Cell);
  if (carriesPointerBounds(V.Type))
    V.BoundsCell = storedPointerCell(V.Address);
  return V;
}

void Frame::staticReference(const Node &N, const std::string &Name,
                            const std::string &Type) {
  if (N.Children.size() != 1 || N.Children.front().K == Node::Tail)
    fail(N.At, "reference requires one initializer");
  const auto &Source = N.Children.front();
  Value Bound;
  if (N.Required) {
    Bound = bindReference(place(Source), Type, N.At);
    symbolicAddress(Bound, N.At);
  }
  // Save the designated address and generation once, in ordinary static
  // initialization order. The reference owns no destruction obligation.
  auto *P = B.getPtrTy();
  auto *Cell = new llvm::GlobalVariable(
      U.M, P, false, llvm::GlobalValue::InternalLinkage,
      llvm::ConstantPointerNull::get(P), "cpn.reference." + Name);
  auto *Ready = new llvm::GlobalVariable(U.M, B.getInt1Ty(), false,
                                         llvm::GlobalValue::InternalLinkage,
                                         B.getFalse(), "cpn.reference.ready");
  auto *FT = llvm::FunctionType::get(B.getVoidTy(), false);
  auto *Fn = llvm::Function::Create(FT, llvm::GlobalValue::InternalLinkage,
                                    "cpn.reference.init", U.M);
  Frame Init(U, nullptr, Fn, Prefix);
  Init.Env = Env;
  Init.Opt = Opt;
  Init.LookupLimit = LookupLimit;
  Init.B.SetInsertPoint(Init.block("entry"));
  auto V = Init.bindReference(Init.place(Source), Type, N.At);
  Init.B.CreateStore(V.Address, Cell);
  V.Lower = V.ElementLower;
  V.Upper = V.ElementUpper;
  Init.saveBounds(Init.storedPointerCell(Cell), V);
  Init.endExpression();
  Init.B.CreateStore(B.getTrue(), Ready);
  Init.B.CreateRetVoid();
  U.Startup.push_back(Fn);
  U.Ready[Cell] = Ready;
  Bound.Type = V.Type;
  Bound.Readonly = V.Readonly;
  Bound.ReferenceCell = Cell;
  U.Globals[Name] = Bound;
}

Value Frame::constantPointerOffset(const Node &N, Value P, Value Other,
                                   const std::string &Element) {
  const auto &DL = U.M.getDataLayout();
  int64_t At;
  if (!P.IR || !P.Lower || !P.Upper)
    fail(N.At, "constant pointer arithmetic requires a known extent");
  auto *Origin = llvm::GetPointerBaseWithConstantOffset(P.IR, At, DL);
  auto position = [&](llvm::Value *Ptr) {
    int64_t Offset;
    if (!Ptr ||
        llvm::GetPointerBaseWithConstantOffset(Ptr, Offset, DL) != Origin)
      fail(N.At, "constant pointers require a common array extent");
    return Offset;
  };
  auto First = position(P.Lower), Last = position(P.Upper);
  auto Stride = DL.getTypeAllocSize(U.ir(Element)).getFixedValue();
  if (llvm::StringRef(Other.Type).ends_with("*")) {
    if (element(P.Type) != element(Other.Type) || N.Text == "+" ||
        position(Other.Lower) != First || position(Other.Upper) != Last)
      fail(N.At, "incompatible constant pointer operands");
    auto Right = position(Other.IR);
    if (N.Text == "-") {
      auto Bytes = llvm::APInt(128, At, true) - llvm::APInt(128, Right, true);
      if (!Bytes.srem(llvm::APInt(128, Stride)).isZero())
        fail(N.At, "pointer difference is not an element count");
      auto Diff = Bytes.sdiv(llvm::APInt(128, Stride));
      if (!Diff.isSignedIntN(64))
        fail(N.At, "pointer difference is not representable");
      return {"isize", B.getInt64(Diff.getSExtValue())};
    }
    return {"bool", B.getInt1(N.Text == "<"    ? At < Right
                              : N.Text == "<=" ? At <= Right
                              : N.Text == ">"  ? At > Right
                                               : At >= Right)};
  }
  if (!integer(Other.Type) || (N.Text != "+" && N.Text != "-"))
    fail(N.At, "pointer offset must be an integer");
  if (Other.Type == "integer")
    Other = convert(Other, "isize", N.At);
  auto *Value = llvm::dyn_cast<llvm::ConstantInt>(Other.IR);
  if (!Value)
    fail(N.At, "constant pointer offset required");
  auto Index = signedType(Other.Type) ? Value->getValue().sextOrTrunc(129)
                                      : Value->getValue().zextOrTrunc(129);
  if (N.Text == "-")
    Index = -Index;
  auto Offset = llvm::APInt(129, At, true) + Index * llvm::APInt(129, Stride);
  if (Offset.slt(llvm::APInt(129, First, true)) ||
      Offset.sgt(llvm::APInt(129, Last, true)))
    fail(N.At, "constant pointer outside its array extent");
  P.IR = llvm::ConstantExpr::getGetElementPtr(
      U.M.getDataLayout(), U.ir(Element), llvm::cast<llvm::Constant>(P.IR),
      B.getInt64(Index.getSExtValue()));
  P.Address = nullptr;
  P.BoundsCell = nullptr;
  P.Prvalue = P.Expiring = true;
  return P;
}
