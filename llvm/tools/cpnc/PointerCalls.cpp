#include "Sema.h"
using namespace cpn;
using llvm::StringRef;

bool cpn::carriesPointerBounds(const std::string &Type) {
  auto T = StringRef(Type).rtrim('&').str();
  return StringRef(unconst(T)).ends_with("*") || T == "storage";
}

// The native function signature stays callable from C. The caller publishes
// the extra CPN metadata only for the dynamic target of this particular call.
// A callee consumes it on entry, so native callbacks and recursion cannot
// inherit an unrelated activation's bounds.
static llvm::GlobalVariable *currentCall(llvm::Module &M) {
  if (auto *Found = M.getGlobalVariable("cpn.pointer.call", true))
    return Found;
  auto *P = llvm::PointerType::getUnqual(M.getContext());
  auto *Header = llvm::StructType::get(M.getContext(), {P, P});
  return new llvm::GlobalVariable(
      M, Header, false, llvm::GlobalValue::InternalLinkage,
      llvm::Constant::getNullValue(Header), "cpn.pointer.call", nullptr,
      llvm::GlobalVariable::GeneralDynamicTLSModel);
}

static llvm::Value *row(llvm::IRBuilder<> &B, llvm::Value *Rows, size_t I) {
  return B.CreateGEP(B.getPtrTy(), Rows, B.getInt32(I));
}

PointerCall Frame::openPointerCall(llvm::Value *Target,
                                   const std::string &Result,
                                   llvm::ArrayRef<std::string> Params,
                                   llvm::ArrayRef<Value> Arguments) {
  if (!carriesPointerBounds(Result) &&
      !llvm::any_of(Params, carriesPointerBounds))
    return {};
  llvm::IRBuilder<> Allocate(IR->getEntryBlock().begin());
  auto *Rows = Allocate.CreateAlloca(
      B.getPtrTy(), B.getInt32(Params.size() + 1), "call.pointer.rows");
  auto bind = [&](size_t Index, const std::string &Type, const Value &V) {
    if (!carriesPointerBounds(Type))
      return;
    llvm::Value *Cell = V.BoundsCell;
    if (!StringRef(Type).ends_with("&") || !Cell) {
      Cell = Allocate.CreateAlloca(pointerMetadataType());
      saveBounds(Cell, V);
    }
    B.CreateStore(Cell, row(B, Rows, Index));
  };
  bind(0, Result, {});
  for (size_t I = 0; I < Params.size(); ++I)
    bind(I + 1, Params[I], Arguments[I]);
  auto *Current = currentCall(U.M);
  auto *Saved = B.CreateLoad(Current->getValueType(), Current);
  auto *Header = B.CreateInsertValue(
      llvm::PoisonValue::get(Current->getValueType()), Target, 0);
  B.CreateStore(B.CreateInsertValue(Header, Rows, 1), Current);
  return {Saved, Rows};
}

void Frame::receivePointerCall() {
  if (!carriesPointerBounds(F->Result) &&
      !llvm::any_of(F->Params, carriesPointerBounds))
    return;
  auto *Current = currentCall(U.M);
  auto *Header = B.CreateLoad(Current->getValueType(), Current);
  auto *Matches = B.CreateICmpEQ(B.CreateExtractValue(Header, 0), IR);
  auto *Missing = llvm::ArrayType::get(B.getPtrTy(), F->Params.size() + 1);
  auto *Fallback = B.CreateAlloca(Missing);
  B.CreateStore(llvm::Constant::getNullValue(Missing), Fallback);
  IncomingPointerRows =
      B.CreateSelect(Matches, B.CreateExtractValue(Header, 1), Fallback);
  B.CreateStore(llvm::Constant::getNullValue(Current->getValueType()), Current);
}

llvm::Value *Frame::incomingPointerCell(size_t Index) {
  auto *Provided =
      B.CreateLoad(B.getPtrTy(), row(B, IncomingPointerRows, Index));
  auto *Fallback = B.CreateAlloca(pointerMetadataType());
  B.CreateStore(llvm::Constant::getNullValue(pointerMetadataType()), Fallback);
  return B.CreateSelect(B.CreateIsNotNull(Provided), Provided, Fallback);
}

void Frame::publishPointerResult(const Value &V) {
  if (!IncomingPointerRows || !carriesPointerBounds(F->Result))
    return;
  // A reference to a pointer shares the caller's metadata cell on assignment.
  if (StringRef(F->Result).ends_with("&") && V.BoundsCell) {
    B.CreateStore(V.BoundsCell, row(B, IncomingPointerRows, 0));
    return;
  }
  saveBounds(incomingPointerCell(0), V);
}

void Frame::closePointerCall(const PointerCall &C) {
  if (C.Previous)
    B.CreateStore(C.Previous, currentCall(U.M));
}

Value Frame::pointerCallResult(Value V, const PointerCall &C,
                               const std::string &Type) {
  if (!C.Rows || !carriesPointerBounds(Type))
    return V;
  V.BoundsCell = B.CreateLoad(B.getPtrTy(), row(B, C.Rows, 0));
  V = load(V);
  if (!StringRef(Type).ends_with("&"))
    V.BoundsCell = nullptr;
  return V;
}

void cpn::forwardPointerCall(llvm::IRBuilder<> &B, llvm::Function *From,
                             llvm::Function *To) {
  auto *Current = currentCall(*From->getParent());
  auto *Header = B.CreateLoad(Current->getValueType(), Current);
  auto *Valid = B.CreateICmpEQ(B.CreateExtractValue(Header, 0), From);
  B.CreateStore(
      B.CreateSelect(Valid, B.CreateInsertValue(Header, To, 0),
                     llvm::Constant::getNullValue(Current->getValueType())),
      Current);
}
