#include "Sema.h"
#include "llvm/AsmParser/Parser.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/SourceMgr.h"
using namespace cpn;

void Context::enableStorage() {
  static constexpr llvm::StringLiteral Runtime =
#include "StorageRuntime.inc"
      ;
  auto Layout = M.getDataLayout();
  auto Triple = M.getTargetTriple();
  llvm::SMDiagnostic Err;
  if (llvm::parseAssemblyInto(
          llvm::MemoryBufferRef(Runtime, "StorageRuntime.ll"), &M, nullptr,
          Err))
    fail({}, Err.getMessage().str());
  M.setDataLayout(Layout);
  M.setTargetTriple(Triple);
  SlotType = llvm::StructType::getTypeByName(C, "cpn.slot");
}
llvm::Constant *Context::typeID(const std::string &T) {
  auto &ID = TypeIDs[T];
  if (!ID)
    ID = new llvm::GlobalVariable(
        M, llvm::Type::getInt8Ty(C), true, llvm::GlobalValue::PrivateLinkage,
        llvm::ConstantInt::get(llvm::Type::getInt8Ty(C), 0), "cpn.type." + T);
  return ID;
}
bool Frame::usesStorage(const Node &N) {
  if (N.K == Node::Call && !N.Children.empty() &&
      N.Children[0].K == Node::Name) {
    auto &S = N.Children[0].Text;
    if (S == "storage_of" || S == "destroy" || S == "abandon" ||
        S == "construct_at")
      return true;
  }
  return llvm::any_of(N.Children, usesStorage) ||
         llvm::any_of(N.Params, usesStorage) ||
         llvm::any_of(N.TemplateArgs, usesStorage);
}
llvm::Function *Context::cleanupEntry(const std::string &Type) {
  if (auto I = CleanupEntries.find(Type); I != CleanupEntries.end())
    return I->second;
  if (!Records.count(Type) && !llvm::StringRef(Type).ends_with("]"))
    return nullptr;
  auto *FT = llvm::FunctionType::get(llvm::Type::getVoidTy(C),
                                     {llvm::PointerType::getUnqual(C)}, false);
  auto *D = llvm::Function::Create(FT, llvm::GlobalValue::InternalLinkage,
                                   "cpn.storage.drop." + Type, M);
  CleanupEntries[Type] = D;
  Frame F(*this, nullptr, D);
  F.B.SetInsertPoint(F.block("entry"));
  F.drop({Type, nullptr, D->getArg(0)});
  F.B.CreateRetVoid();
  return D;
}
namespace {
enum SlotField {
  Address = 3,
  CurrentType = 5,
  Stamp = 7,
  Destructor = 8,
  Capacity = 9,
  Alignment = 10,
  Birth = 6
};
llvm::Constant *destructor(Frame &F, const std::string &T) {
  if (auto *D = F.U.cleanupEntry(T))
    return D;
  return llvm::ConstantPointerNull::get(F.B.getPtrTy());
}
} // namespace
llvm::Value *Frame::slotFor(Value V) {
  if (V.Slot)
    return V.Slot;
  return B.CreateCall(U.M.getFunction("cpn.slot.find"),
                      {V.Address, U.typeID(V.Type),
                       llvm::ConstantPointerNull::get(B.getPtrTy()),
                       B.getFalse()});
}
void Frame::track(Value &V, llvm::GlobalVariable *GlobalSlot) {
  if (!TracksStorage)
    return;
  auto *Ty = U.ir(V.Type);
  const auto &DL = U.M.getDataLayout();
  if (GlobalSlot)
    V.Slot = GlobalSlot;
  else {
    llvm::IRBuilder<> Entry(IR->getEntryBlock().begin());
    V.Slot = Entry.CreateAlloca(U.SlotType);
  }
  B.CreateCall(U.M.getFunction("cpn.slot.begin"),
               {V.Slot, V.Address, U.typeID(V.Type), destructor(*this, V.Type),
                B.getInt64(DL.getTypeAllocSize(Ty).getFixedValue()),
                B.getInt64(DL.getABITypeAlign(Ty).value()),
                llvm::ConstantPointerNull::get(B.getPtrTy()), B.getInt64(0)});
  B.CreateCall(U.M.getFunction("cpn.slot.link"), {V.Slot});
  V.ExtentType = V.Type;
  if (!GlobalSlot) {
    V.Generation =
        B.CreateCall(U.M.getFunction("cpn.generation"), {V.Slot, B.getTrue()});
    Registrations[V.Storage] = {V.Slot};
  }
}
Value Frame::subobject(Value Parent, Value V) {
  V.Origins = Parent.Origins;
  if (!TracksStorage || !Parent.Address || !V.Address)
    return V;
  const auto &DL = U.M.getDataLayout();
  auto *Ty = U.ir(V.Type);
  V.Slot = B.CreateCall(U.M.getFunction("cpn.slot.child"),
                        {slotFor(Parent), V.Address, U.typeID(V.Type),
                         destructor(*this, V.Type),
                         B.getInt64(DL.getTypeAllocSize(Ty).getFixedValue()),
                         B.getInt64(DL.getABITypeAlign(Ty).value())});
  V.Generation =
      B.CreateCall(U.M.getFunction("cpn.generation"), {V.Slot, B.getTrue()});
  V.Storage = Parent.Storage;
  V.ExtentType = V.Type;
  V.Subobject = true;
  return V;
}
void Frame::dropChild(Value Parent, Value V, bool AsBase) {
  if (AsBase && U.Whole) {
    auto *Run = block("base.scheduled"), *Done = block("base.done");
    B.CreateCondBr(B.CreateCall(U.M.getFunction("cpn.view.available"),
                                {V.Address, U.typeID(V.Type), B.getTrue()}),
                   Run, Done);
    B.SetInsertPoint(Run);
    drop(V, true);
    branch(Done);
    B.SetInsertPoint(Done);
    return;
  }
  if (!TracksStorage || AsBase) {
    drop(V, AsBase);
    return;
  }
  // Looking up a registration during the sweep does not create one.
  auto *Slot =
      B.CreateCall(U.M.getFunction("cpn.slot.find"),
                   {V.Address, U.typeID(V.Type), slotFor(Parent), B.getTrue()});
  auto *Registered = block("slot.registered"),
       *Original = block("slot.original"), *Done = block("slot.done");
  B.CreateCondBr(B.CreateIsNotNull(Slot), Registered, Original);
  B.SetInsertPoint(Registered);
  B.CreateCall(U.M.getFunction("cpn.slot.retire"), {Slot, B.getTrue()});
  branch(Done);
  B.SetInsertPoint(Original);
  drop(V);
  branch(Done);
  B.SetInsertPoint(Done);
}
void Frame::ensureLive(const Value &V, const Token &At) {
  if (!V.Storage.empty() && Active.count(V.Storage) &&
      Active.at(V.Storage) == 0)
    fail(At, "ended object generation");
  if (!IR || !V.Slot)
    return;
  auto *Expected = V.Generation ? V.Generation : B.getInt64(0);
  guard(B.CreateNot(
      B.CreateCall(U.M.getFunction("cpn.borrow.valid"), {V.Slot, Expected})));
}
void Frame::retireStorage(const Value &V, bool Destroy) {
  B.CreateCall(U.M.getFunction("cpn.slot.retire"),
               {V.Slot, B.getInt1(Destroy)});
  if (!V.Subobject && !V.Storage.empty())
    Active[V.Storage] = 0;
}
void Frame::replaceGeneration(const Value &V, const std::string &T,
                              const Token &) {
  auto *S = V.Slot;
  B.CreateStore(U.typeID(T), B.CreateStructGEP(U.SlotType, S, CurrentType));
  B.CreateStore(destructor(*this, T),
                B.CreateStructGEP(U.SlotType, S, Destructor));
  B.CreateStore(B.CreateCall(U.M.getFunction("cpn.new.generation")),
                B.CreateStructGEP(U.SlotType, S, Stamp));
  if (!V.Subobject && !V.Storage.empty())
    Active[V.Storage] = 1;
}
Value Frame::storageCall(const Node &C, const std::vector<Node> &Args) {
  if (!TracksStorage)
    fail(C.At, "storage operation requires runtime object storage");
  if (C.Text == "construct_at") {
    auto S = eval(Args.front());
    if (S.Type != "storage" || !S.Slot)
      fail(C.At, "storage view required");
    if (!S.Subobject && Active.count(S.Storage) && Active[S.Storage] == 1)
      fail(C.At, "storage contains a live generation");
    guard(B.CreateNot(B.CreateCall(U.M.getFunction("cpn.extent.valid"),
                                   {S.Slot, S.Generation})));
    auto *Current =
        B.CreateCall(U.M.getFunction("cpn.generation"), {S.Slot, B.getFalse()});
    guard(B.CreateTrunc(Current, B.getInt1Ty()));
    const auto T = resolve(C.TemplateArgs.front().Type, C.At);
    const auto &DL = U.M.getDataLayout();
    auto *Ty = U.ir(T, C.At);
    if (!Ty->isSized())
      fail(C.At, "replacement requires a complete object type");
    auto Size = DL.getTypeAllocSize(Ty).getFixedValue(),
         Align = DL.getABITypeAlign(Ty).value();
    if (!S.ExtentType.empty()) {
      auto *Extent = U.ir(S.ExtentType);
      if (DL.getTypeAllocSize(Extent).getFixedValue() < Size ||
          DL.getABITypeAlign(Extent).value() < Align)
        fail(C.At, "insufficient storage capacity");
    }
    auto loadBound = [&](SlotField Index) {
      return B.CreateLoad(B.getInt64Ty(),
                          B.CreateStructGEP(U.SlotType, S.Slot, Index));
    };
    guard(B.CreateOr(B.CreateICmpULT(loadBound(Capacity), B.getInt64(Size)),
                     B.CreateICmpULT(loadBound(Alignment), B.getInt64(Align))));
    construct(T, {Args.begin() + 1, Args.end()}, C.At, S.IR);
    replaceGeneration(S, T, C.At);
    Value P{T + "*", S.IR};
    P.borrow(S);
    P.Generation =
        B.CreateCall(U.M.getFunction("cpn.generation"), {S.Slot, B.getFalse()});
    return P;
  }
  bool Storage = C.Text == "storage_of";
  Value V = place(Args.front(), !Storage);
  if (!V.Slot)
    V.Slot = slotFor(V);
  guard(B.CreateIsNull(V.Slot));
  if (Storage) {
    guard(B.CreateNot(
        B.CreateCall(U.M.getFunction("cpn.slot.linked"), {V.Slot})));
    Value S{"storage",
            B.CreateLoad(B.getPtrTy(),
                         B.CreateStructGEP(U.SlotType, V.Slot, Address))};
    S.borrow(V);
    S.Generation = B.CreateLoad(B.getInt64Ty(),
                                B.CreateStructGEP(U.SlotType, V.Slot, Birth));
    return S;
  }
  if (V.BaseView && V.ExtentType != V.Type &&
      (!U.Records.count(V.Type) || !U.Records.at(V.Type).VirtualDestructor))
    fail(C.At,
         "complete destruction through a base requires virtual destruction");
  if (C.Text == "abandon")
    checkAbandon(V.Type, C.At);
  retireStorage(V, C.Text == "destroy");
  return {"void"};
}
void Frame::joinStorage(const std::map<std::string, int> &Other) {
  for (auto &[ID, Live] : Active) {
    auto I = Other.find(ID);
    if (I != Other.end() && I->second != Live)
      Live = -1;
  }
}
void Frame::forgetStorage() {
  for (auto &[ID, State] : Active)
    if (Registrations.count(ID))
      State = -1;
}

// Array positions share the parent extent. Changing position selects the
// destination element's generation, while the one-past address has no slot.
void Frame::offsetRegistration(Value &P, llvm::Value *Target,
                               const std::string &Element, const Token &At) {
  if (!TracksStorage || !P.ArraySlot || !P.Upper)
    return;
  Value Owner{Element, nullptr, P.Lower};
  Owner.Slot = P.ArraySlot;
  Owner.Generation = P.ArrayGeneration;
  ensureLive(Owner, At);
  auto *From = B.GetInsertBlock(), *ElementPath = block("pointer.element"),
       *Done = block("pointer.position");
  auto *Past = B.CreateICmpEQ(Target, P.Upper);
  auto *Changed = B.CreateICmpNE(Target, P.IR);
  auto *Null = llvm::ConstantPointerNull::get(B.getPtrTy());
  auto *Slot = B.CreateSelect(Past, Null, P.Slot ? P.Slot : Null);
  auto *Stamp = B.CreateSelect(Past, B.getInt64(0),
                               P.Generation ? P.Generation : B.getInt64(0));
  auto *HasElement =
      B.CreateAnd(B.CreateIsNotNull(P.ArraySlot), B.CreateNot(Past));
  B.CreateCondBr(B.CreateAnd(HasElement, Changed), ElementPath, Done);
  B.SetInsertPoint(ElementPath);
  auto V = subobject(Owner, {Element, nullptr, Target});
  auto *Exit = B.GetInsertBlock();
  branch(Done);
  B.SetInsertPoint(Done);
  auto *NewSlot = B.CreatePHI(B.getPtrTy(), 2);
  NewSlot->addIncoming(Slot, From);
  NewSlot->addIncoming(V.Slot, Exit);
  auto *NewStamp = B.CreatePHI(B.getInt64Ty(), 2);
  NewStamp->addIncoming(Stamp, From);
  NewStamp->addIncoming(V.Generation, Exit);
  P.Slot = NewSlot;
  P.Generation = NewStamp;
}
