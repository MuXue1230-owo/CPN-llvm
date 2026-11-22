#include "Sema.h"
using namespace llvm;
using namespace cpn;

namespace {
// An object's native representation stays available to C. Its pointer slots
// have a parallel array of metadata owned by the same activation or global.
// The type-specific map translates a byte offset into that compact array.
struct Layout {
  uint64_t Count = 0;
  llvm::Function *Index = nullptr;
};
class Layouts {
  cpn::Context &U;
  std::map<Type *, Layout> Cache;
  std::map<Type *, std::string> Unions;
  IntegerType *I64;
  const DataLayout &DL;

public:
  explicit Layouts(cpn::Context &U)
      : U(U), I64(Type::getInt64Ty(U.C)), DL(U.M.getDataLayout()) {
    for (auto &[Name, Cases] : U.Variants)
      Unions.emplace(U.Records.at(Name).IR, Name);
  }
  Layout get(Type *T) {
    if (auto Found = Cache.find(T); Found != Cache.end())
      return Found->second;
    if (!T->isSized())
      return {};
    struct Part {
      uint64_t Offset, Bytes, First;
      Layout Child;
    };
    std::vector<Part> Parts;
    uint64_t Count = 0, Stride = 0;
    bool Dense = T->isPointerTy();
    if (auto It = Unions.find(T); It != Unions.end()) {
      // Payloads overlap. Every naturally aligned pointer position in the
      // union uses the same cell across all active-case transitions.
      Dense = llvm::any_of(U.Variants.at(It->second), [&](const auto &K) {
        return get(U.Cases.at(K).Payload).Count != 0;
      });
    } else if (auto *AT = dyn_cast<ArrayType>(T)) {
      auto *E = AT->getElementType();
      auto Child = get(E);
      if (Child.Count && AT->getNumElements()) {
        Stride = DL.getTypeAllocSize(E).getFixedValue();
        Count = Child.Count * AT->getNumElements();
        Parts.push_back({0, Stride, 0, Child});
      }
    } else if (auto *ST = dyn_cast<StructType>(T)) {
      for (unsigned I = 0; I < ST->getNumElements(); ++I) {
        Type *E = ST->getElementType(I);
        auto Child = get(E);
        if (!Child.Count)
          continue;
        Parts.push_back({DL.getStructLayout(ST)->getElementOffset(I),
                         DL.getTypeAllocSize(E).getFixedValue(), Count, Child});
        Count += Child.Count;
      }
    }
    auto Width = DL.getPointerSize();
    if (Dense)
      Count = DL.getTypeAllocSize(T).getFixedValue() / Width;
    if (!Count)
      return Cache[T] = {};
    auto *FT = FunctionType::get(I64, {I64}, false);
    auto *F = llvm::Function::Create(FT, GlobalValue::InternalLinkage,
                                     "cpn.pointer.index", U.M);
    IRBuilder<> B(BasicBlock::Create(U.C, "entry", F));
    auto *Offset = F->getArg(0);
    auto *Invalid = B.getInt64(-1);
    if (Dense) {
      auto *Aligned = B.CreateICmpEQ(B.CreateURem(Offset, B.getInt64(Width)),
                                     B.getInt64(0));
      B.CreateRet(B.CreateSelect(
          Aligned, B.CreateUDiv(Offset, B.getInt64(Width)), Invalid));
    } else if (Stride) {
      auto &P = Parts.front();
      auto *Index = B.CreateCall(P.Child.Index,
                                 {B.CreateURem(Offset, B.getInt64(Stride))});
      auto *Base = B.CreateMul(B.CreateUDiv(Offset, B.getInt64(Stride)),
                               B.getInt64(P.Child.Count));
      B.CreateRet(B.CreateSelect(B.CreateICmpEQ(Index, Invalid), Invalid,
                                 B.CreateAdd(Base, Index)));
    } else {
      for (auto &P : Parts) {
        auto *In = BasicBlock::Create(U.C, "field", F);
        auto *Next = BasicBlock::Create(U.C, "next", F);
        auto *Delta = B.CreateSub(Offset, B.getInt64(P.Offset));
        B.CreateCondBr(B.CreateICmpULT(Delta, B.getInt64(P.Bytes)), In, Next);
        B.SetInsertPoint(In);
        auto *Index = B.CreateCall(P.Child.Index, {Delta});
        B.CreateRet(B.CreateSelect(B.CreateICmpEQ(Index, Invalid), Invalid,
                                   B.CreateAdd(Index, B.getInt64(P.First))));
        B.SetInsertPoint(Next);
      }
      B.CreateRet(Invalid);
    }
    return Cache[T] = {Count, F};
  }
};
} // namespace

llvm::Value *Frame::storedPointerCell(llvm::Value *Address) {
  auto *Ptr = B.getPtrTy();
  auto Lookup = U.M.getOrInsertFunction("cpn.pointer.field", Ptr, Ptr, Ptr);
  IRBuilder<> Entry(IR->getEntryBlock().begin());
  auto *Fallback = Entry.CreateAlloca(pointerMetadataType());
  B.CreateStore(Constant::getNullValue(pointerMetadataType()), Fallback);
  return B.CreateCall(Lookup, {Address, Fallback});
}

void cpn::Context::finishPointerStorage() {
  auto *Lookup = M.getFunction("cpn.pointer.field");
  if (!Lookup)
    return;
  Lookup->setLinkage(GlobalValue::InternalLinkage);
  IRBuilder<> B(BasicBlock::Create(C, "entry", Lookup));
  auto *P = B.getPtrTy();
  auto *I = B.getInt64Ty();
  Frame F(*this, nullptr, Lookup);
  auto *Meta = F.pointerMetadataType();
  auto *Row = StructType::get(C, {P, P, I, P, P});
  auto *Null = ConstantPointerNull::get(P);
  auto *Head = new GlobalVariable(M, P, false, GlobalValue::InternalLinkage,
                                  Null, "cpn.pointer.objects", nullptr,
                                  GlobalVariable::GeneralDynamicTLSModel);
  auto *Entry = B.GetInsertBlock();
  auto *Scan = BasicBlock::Create(C, "scan", Lookup);
  auto *Check = BasicBlock::Create(C, "extent", Lookup);
  auto *Resolve = BasicBlock::Create(C, "resolve", Lookup);
  auto *Found = BasicBlock::Create(C, "found", Lookup);
  auto *Advance = BasicBlock::Create(C, "advance", Lookup);
  auto *Missing = BasicBlock::Create(C, "missing", Lookup);
  auto *First = B.CreateLoad(P, Head);
  B.CreateBr(Scan);
  B.SetInsertPoint(Scan);
  auto *Item = B.CreatePHI(P, 2);
  Item->addIncoming(First, Entry);
  B.CreateCondBr(B.CreateIsNull(Item), Missing, Check);
  B.SetInsertPoint(Check);
  auto read = [&](unsigned N) {
    return B.CreateLoad(Row->getElementType(N),
                        B.CreateStructGEP(Row, Item, N));
  };
  auto *Delta = B.CreateSub(B.CreatePtrToInt(Lookup->getArg(0), I),
                            B.CreatePtrToInt(read(1), I));
  B.CreateCondBr(B.CreateICmpULT(Delta, read(2)), Resolve, Advance);
  B.SetInsertPoint(Resolve);
  auto *Index =
      B.CreateCall(FunctionType::get(I, {I}, false), read(4), {Delta});
  B.CreateCondBr(B.CreateICmpEQ(Index, B.getInt64(-1)), Missing, Found);
  B.SetInsertPoint(Found);
  B.CreateRet(B.CreateGEP(Meta, read(3), Index));
  B.SetInsertPoint(Advance);
  Item->addIncoming(read(0), Advance);
  B.CreateBr(Scan);
  B.SetInsertPoint(Missing);
  B.CreateRet(Lookup->getArg(1));

  Layouts Types(*this);
  std::set<GlobalVariable *> Seen;
  Constant *GlobalHead = Null;
  for (auto &[Name, V] : Globals) {
    auto *G = V.ReferenceCell ? V.ReferenceCell
                              : dyn_cast_or_null<GlobalVariable>(V.Address);
    if (!G || !Seen.insert(G).second)
      continue;
    auto *T = G->getValueType();
    auto L = Types.get(T);
    if (!L.Count)
      continue;
    auto *Cells = ArrayType::get(Meta, L.Count);
    auto *Data =
        new GlobalVariable(M, Cells, false, GlobalValue::InternalLinkage,
                           Constant::getNullValue(Cells), "cpn.pointer.cells");
    GlobalHead = new GlobalVariable(
        M, Row, true, GlobalValue::InternalLinkage,
        ConstantStruct::get(
            Row,
            {GlobalHead, G,
             B.getInt64(M.getDataLayout().getTypeAllocSize(T).getFixedValue()),
             Data, L.Index}),
        "cpn.pointer.object");
  }
  Head->setInitializer(GlobalHead);
  for (auto &Fn : M) {
    if (Fn.empty())
      continue;
    auto &Block = Fn.getEntryBlock();
    std::vector<std::pair<AllocaInst *, Layout>> Objects;
    for (auto &Inst : Block)
      if (auto *A = dyn_cast<AllocaInst>(&Inst);
          A && A->getMetadata("cpn.object")) {
        A->setMetadata("cpn.object", nullptr);
        auto L = Types.get(A->getAllocatedType());
        if (L.Count)
          Objects.emplace_back(A, L);
      }
    if (Objects.empty())
      continue;
    // Keep the registered extents live for the activation. Construction writes
    // each pointer's metadata anew when a lexical slot is reused in a loop.
    for (auto &[A, L] : Objects)
      if (A != &Block.front())
        A->moveBefore(Block, Block.begin());
    B.SetInsertPoint(Objects.front().first->getNextNode());
    auto *Previous = B.CreateLoad(P, Head);
    llvm::Value *Current = Previous;
    for (auto &[A, L] : Objects) {
      auto *Storage = ArrayType::get(Meta, L.Count);
      auto *Cells = B.CreateAlloca(Storage);
      B.CreateMemSet(
          Cells, B.getInt8(0),
          M.getDataLayout().getTypeAllocSize(Storage).getFixedValue(),
          M.getDataLayout().getABITypeAlign(Meta));
      auto *Node = B.CreateAlloca(Row);
      auto set = [&](unsigned N, llvm::Value *Value) {
        B.CreateStore(Value, B.CreateStructGEP(Row, Node, N));
      };
      set(0, Current);
      set(1, A);
      set(2, B.getInt64(M.getDataLayout()
                            .getTypeAllocSize(A->getAllocatedType())
                            .getFixedValue()));
      set(3, Cells);
      set(4, L.Index);
      Current = Node;
    }
    B.CreateStore(Current, Head);
    for (auto &BB : Fn)
      if (auto *Ret = dyn_cast<ReturnInst>(BB.getTerminator())) {
        B.SetInsertPoint(Ret);
        B.CreateStore(Previous, Head);
      }
  }
}

// Prvalue relocation copies the representation without invoking an authored
// copy or move. Carry the metadata for the same byte positions as well.
void Frame::copyStoredBounds(cpn::Value Source, llvm::Value *Dest) {
  const auto &DL = U.M.getDataLayout();
  auto Width = DL.getPointerSize();
  auto Size = DL.getTypeAllocSize(U.ir(Source.Type)).getFixedValue();
  if (Size < Width || DL.getABITypeAlign(U.ir(Source.Type)) < Align(Width))
    return;
  auto *Before = B.GetInsertBlock(), *Loop = block("pointer.copy"),
       *Done = block("pointer.copied");
  branch(Loop);
  B.SetInsertPoint(Loop);
  auto *Offset = B.CreatePHI(B.getInt64Ty(), 2);
  Offset->addIncoming(B.getInt64(0), Before);
  auto cell = [&](llvm::Value *P) {
    return storedPointerCell(B.CreateGEP(B.getInt8Ty(), P, Offset));
  };
  auto *From = cell(Source.Address), *To = cell(Dest);
  B.CreateStore(B.CreateLoad(pointerMetadataType(), From), To);
  auto *Next = B.CreateAdd(Offset, B.getInt64(Width));
  Offset->addIncoming(Next, B.GetInsertBlock());
  B.CreateCondBr(B.CreateICmpULE(Next, B.getInt64(Size - Width)), Loop, Done);
  B.SetInsertPoint(Done);
}
