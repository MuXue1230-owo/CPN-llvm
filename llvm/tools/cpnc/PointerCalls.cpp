#include "Sema.h"
using namespace cpn;
using llvm::StringRef;

bool cpn::carriesPointerBounds(const std::string &Type) {
  auto T = StringRef(Type).rtrim('&').str();
  return StringRef(unconst(T)).ends_with("*") || unconst(T) == StorageViewType;
}

bool cpn::carriesBorrow(const std::string &Type) {
  return carriesPointerBounds(Type) || StringRef(Type).ends_with("&");
}
static Value metadataFor(const std::string &Type, Value V) {
  if (!carriesPointerBounds(Type) && StringRef(Type).ends_with("&")) {
    V.Lower = V.ElementLower;
    V.Upper = V.ElementUpper;
  }
  return V;
}

// The pointer stored in a variable and the extent designated by a reference
// to an array element have distinct bounds. Preserve the original generation
// even if another argument reconstructs the same physical address.
void Frame::readReferent(Value &V, llvm::Value *Cell) {
  Value Metadata;
  readBounds(Metadata, Cell);
  V.ElementLower = Metadata.Lower;
  V.ElementUpper = Metadata.Upper;
  V.ArraySlot = Metadata.ArraySlot;
  V.ArrayGeneration = Metadata.ArrayGeneration;
  if (TracksStorage) {
    if (V.Slot) {
      auto *Provided = B.CreateIsNotNull(Metadata.Slot);
      V.Slot = B.CreateSelect(Provided, Metadata.Slot, V.Slot);
      V.Generation =
          B.CreateSelect(Provided, Metadata.Generation, V.Generation);
    } else {
      V.Slot = Metadata.Slot;
      V.Generation = Metadata.Generation;
    }
  }
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

llvm::SmallVector<llvm::OperandBundleDef, 1>
Frame::storageArgumentBundles(llvm::ArrayRef<std::string> Params,
                              llvm::ArrayRef<Value> Arguments,
                              unsigned ABIHeaders) {
  llvm::SmallVector<llvm::Value *, 6> StorageArguments;
  if (TracksStorage)
    for (auto [I, Type] : llvm::enumerate(Params)) {
      const bool Reference = StringRef(Type).ends_with("&");
      if (!Reference && !StringRef(Type).ends_with("*"))
        continue;
      auto Designation =
          Reference ? Arguments[I].objectDesignation() : Arguments[I];
      if (!Designation.Slot)
        continue;
      StorageArguments.push_back(B.getInt32(ABIHeaders + I));
      StorageArguments.push_back(Designation.Slot);
      StorageArguments.push_back(Designation.Generation ? Designation.Generation
                                                        : B.getInt64(0));
    }
  llvm::SmallVector<llvm::OperandBundleDef, 1> Bundles;
  if (!StorageArguments.empty())
    Bundles.emplace_back(StorageArgumentBundle, StorageArguments);
  return Bundles;
}

PointerCall Frame::openPointerCall(llvm::Value *Target,
                                   const std::string &Result,
                                   llvm::ArrayRef<std::string> Params,
                                   llvm::ArrayRef<Value> Arguments) {
  if (!carriesBorrow(Result) && !llvm::any_of(Params, carriesBorrow))
    return {};
  llvm::IRBuilder<> Allocate(IR->getEntryBlock().begin());
  auto *Rows = Allocate.CreateAlloca(
      B.getPtrTy(), B.getInt32(Params.size() + 1), "call.pointer.rows");
  auto bind = [&](size_t Index, const std::string &Type, const Value &V) {
    if (!carriesBorrow(Type))
      return;
    // Admission of a later argument can change the lifetime of an earlier
    // argument's pointer cell. Validate that cell before entering the callee.
    if (StringRef(Type).ends_with("&") && V.PointerCell)
      ensureLive(V, {});
    llvm::Value *Cell = carriesPointerBounds(Type) ? V.BoundsCell : nullptr;
    if (!StringRef(Type).ends_with("&") || !Cell) {
      Cell = Allocate.CreateAlloca(pointerMetadataType());
      saveBounds(Cell, metadataFor(Type, V));
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
  if (!carriesBorrow(F->Result) && !llvm::any_of(F->Params, carriesBorrow))
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
  if (!IncomingPointerRows || !carriesBorrow(F->Result))
    return;
  // A reference to a pointer shares the caller's metadata cell on assignment.
  if (StringRef(F->Result).ends_with("&") && carriesPointerBounds(F->Result) &&
      V.BoundsCell) {
    B.CreateStore(V.BoundsCell, row(B, IncomingPointerRows, 0));
    return;
  }
  saveBounds(incomingPointerCell(0), metadataFor(F->Result, V));
}

void Frame::closePointerCall(const PointerCall &C) {
  if (C.Previous)
    B.CreateStore(C.Previous, currentCall(U.M));
}

Value Frame::pointerCallResult(Value V, const PointerCall &C,
                               const std::string &Type) {
  if (!C.Rows || !carriesBorrow(Type))
    return V;
  auto *Cell = B.CreateLoad(B.getPtrTy(), row(B, C.Rows, 0));
  if (!carriesPointerBounds(Type)) {
    readReferent(V, Cell);
    return load(V);
  }
  V.BoundsCell = Cell;
  if (TracksStorage && StringRef(Type).ends_with("&") && V.Address) {
    V.Slot = slotFor(V);
    V.Generation =
        B.CreateCall(U.M.getFunction("cpn.generation"), {V.Slot, B.getFalse()});
    V.rememberPointerCell(V);
  }
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
