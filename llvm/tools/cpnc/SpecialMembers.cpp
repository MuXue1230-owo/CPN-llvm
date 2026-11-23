#include "Sema.h"
using namespace cpn;
namespace {
bool assignment(SpecialOperation Op) {
  return Op == SpecialOperation::CopyAssign ||
         Op == SpecialOperation::MoveAssign;
}
bool moving(SpecialOperation Op) {
  return Op == SpecialOperation::MoveAssign ||
         Op == SpecialOperation::MoveConstruct;
}
const char *operationName(SpecialOperation Op) {
  switch (Op) {
  case SpecialOperation::CopyConstruct:
    return "copy constructor";
  case SpecialOperation::MoveConstruct:
    return "move constructor";
  case SpecialOperation::CopyAssign:
    return "copy assignment";
  case SpecialOperation::MoveAssign:
    return "move assignment";
  }
  llvm_unreachable("invalid special operation");
}
} // namespace

bool Frame::constructible(const std::string &T, SpecialOperation Op,
                          const Token &At) {
  if (auto Mutable = unconst(T); Mutable != T)
    return !assignment(Op) && constructible(Mutable, Op, At);
  if (llvm::StringRef(T).ends_with("]"))
    return llvm::StringRef(T).ends_with("[0]") ||
           constructible(element(T), Op, At);
  auto I = U.Records.find(T);
  if (I == U.Records.end())
    return U.ir(T, At)->isSized();
  auto &R = I->second;
  if (!R.Complete)
    return false;
  if (R.Decl.K != Node::Lambda) {
    auto Member = R.Special.find(Op);
    if (Member == R.Special.end())
      return false;
    auto &Decl = Member->second.Decl;
    try {
      checkAccess(Decl, T, At);
    } catch (const Diagnostic &) {
      return false;
    }
    if (auto C = Decl.Settings.find("control");
        C != Decl.Settings.end() && C->second == "delete")
      return false;
    if (Member->second.Body)
      return true;
  }
  if (R.Decl.K == Node::Union)
    for (const auto &Key : U.Variants.at(T))
      for (const auto &Field : U.Cases.at(Key).Types)
        if (!constructible(Field, Op, At))
          return false;
  return llvm::all_of(R.Fields, [&](auto &Field) {
    return !(assignment(Op) && Field.Decl.Const) &&
           constructible(Field.Type, Op, At);
  });
}
void Frame::transfer(Value Source, llvm::Value *Dest, SpecialOperation Op,
                     const Token &At, bool AsBase, bool CheckInvariant) {
  if (auto Mutable = unconst(Source.Type); Mutable != Source.Type) {
    if (assignment(Op))
      fail(At, "assignment to a const subobject");
    Source.Type = Mutable;
    Source.Readonly = true;
  }
  auto *Ty = U.ir(Source.Type, At);
  if (auto *Array = llvm::dyn_cast<llvm::ArrayType>(Ty)) {
    if (llvm::StringRef(Source.Type).ends_with("[0]"))
      return;
    // Evaluate aggregate designators once. Each element's own declared
    // operation executes before continuing to the next element.
    auto Elem = element(Source.Type);
    if (carriesPointerBounds(Elem) || U.Records.count(unconst(Elem)) ||
        llvm::isa<llvm::ArrayType>(Array->getElementType())) {
      auto *Progress =
          assignment(Op)
              ? nullptr
              : beginConstructionPrefix({Source.Type, nullptr, Dest});
      auto *Preheader = B.GetInsertBlock(), *Loop = block("array.transfer"),
           *Done = block("array.done");
      branch(Loop);
      B.SetInsertPoint(Loop);
      auto *Index = B.CreatePHI(B.getInt64Ty(), 2);
      Index->addIncoming(B.getInt64(0), Preheader);
      auto *From = B.CreateGEP(Array, Source.Address, {B.getInt32(0), Index});
      auto *To = B.CreateGEP(Array, Dest, {B.getInt32(0), Index});
      transfer({Elem, nullptr, From, Source.Readonly}, To, Op, At);
      auto *Next = B.CreateAdd(Index, B.getInt64(1));
      if (Progress)
        B.CreateStore(Next, Progress);
      Index->addIncoming(Next, B.GetInsertBlock());
      B.CreateCondBr(B.CreateICmpULT(Next, B.getInt64(Array->getNumElements())),
                     Loop, Done);
      B.SetInsertPoint(Done);
      endConstructionPrefix(Progress);
      return;
    }
    const auto &Layout = U.M.getDataLayout();
    B.CreateMemMove(Dest, Layout.getABITypeAlign(Ty), Source.Address,
                    Layout.getABITypeAlign(Ty),
                    Layout.getTypeAllocSize(Ty).getFixedValue());
    return;
  }
  auto It = U.Records.find(Source.Type);
  if (It == U.Records.end()) {
    Source = load(Source);
    if (carriesPointerBounds(Source.Type))
      saveBounds(storedPointerCell(Dest), Source);
    B.CreateStore(Source.IR, Dest);
    return;
  }
  auto &R = It->second;
  Value Result{Source.Type, nullptr, Dest};
  Result.BaseView = AsBase;
  auto *Previous = assignment(Op) ? nullptr : pushInvariantLifetime(Result);
  if (!assignment(Op) && !AsBase)
    bindVirtualLayout(Result);
  if (!assignment(Op))
    enterOwnerLayer(Result);
  if (moving(Op) && Source.Readonly)
    fail(At, "moving requires a mutable source");
  bool PublicAssignment = false;
  auto Complete = [&] {
    popInvariantLifetime(Previous);
    if (CheckInvariant && (!assignment(Op) || PublicAssignment))
      checkInvariants(Result);
  };
  if (R.Decl.K != Node::Lambda) {
    auto I = R.Special.find(Op);
    if (I == R.Special.end())
      fail(At, std::string("no available ") + operationName(Op) + " for " +
                   Source.Type);
    auto &Member = I->second;
    checkAccess(Member.Decl, Source.Type, At);
    auto Access = Member.Decl.Settings.find("access");
    PublicAssignment =
        assignment(Op) &&
        (Access == Member.Decl.Settings.end() || Access->second == "public");
    if (Member.Decl.Settings.count("control") &&
        Member.Decl.Settings.at("control") == "delete")
      fail(At, std::string("selected ") + operationName(Op) + " is deleted");
    if (Member.Body) {
      Source.Expiring = moving(Op);
      invoke(*Member.Body, {Source}, At, Result);
      if (!assignment(Op))
        Complete();
      return;
    }
  }
  if (PublicAssignment)
    checkInvariants(Result);
  if (R.Decl.K == Node::Union) {
    transferPayload(Source, Dest, Op, At);
    Complete();
    return;
  }
  if (!assignment(Op) && R.Fields.empty())
    B.CreateStore(llvm::Constant::getNullValue(Ty), Dest);
  auto *Progress = assignment(Op) ? nullptr : beginConstructionPrefix(Result);
  for (size_t I = AsBase ? R.VirtualCount : 0; I < R.Fields.size(); ++I) {
    auto &Field = R.Fields[I];
    auto *From = fieldAddress(Source, I);
    auto *To = fieldAddress(Result, I);
    transfer({Field.Type, nullptr, From, Source.Readonly}, To, Op, At,
             I < R.Bases.size());
    if (!assignment(Op))
      finishVirtualBase(Result, I);
    if (Progress)
      B.CreateStore(B.getInt64(I + 1), Progress);
  }
  endConstructionPrefix(Progress);
  if (!assignment(Op))
    installTables(Result);
  Complete();
}

Value Frame::materialize(Value Source, const Token &At, llvm::Value *Dest,
                         bool CheckInvariant) {
  if (!IR) {
    Source = load(Source);
    if (Source.Prvalue)
      consume(Source);
    if (!Source.Prvalue && U.aggregate(Source.Type))
      return constantCopy(Source, At, CheckInvariant);
    Source.Location.reset();
    Source.ConstantTemporary.reset();
    Source.Address = nullptr;
    return Source;
  }
  bool Aggregate = U.aggregate(Source.Type);
  if (Dest && Dest == Source.Address)
    return Source;
  if (!Aggregate || !Source.Address || Source.Prvalue) {
    if (Source.Prvalue)
      consume(Source);
    if (Dest) {
      if (carriesPointerBounds(Source.Type)) {
        Source = load(Source);
        saveBounds(storedPointerCell(Dest), Source);
      } else if (Aggregate && Source.Address)
        copyStoredBounds(Source, Dest);
      if (llvm::StringRef(Source.Type).ends_with("]") && Source.Address) {
        const auto &Layout = U.M.getDataLayout();
        auto *Ty = U.ir(Source.Type);
        B.CreateMemMove(Dest, Layout.getABITypeAlign(Ty), Source.Address,
                        Layout.getABITypeAlign(Ty),
                        Layout.getTypeAllocSize(Ty).getFixedValue());
        Source.Address = Dest;
      } else if (Source.Prvalue && Source.Address &&
                 U.Records.count(Source.Type) &&
                 U.Records.at(Source.Type).VirtualCount)
        B.CreateStore(B.CreateLoad(U.ir(Source.Type), Source.Address), Dest);
      else
        B.CreateStore(load(Source).IR, Dest);
    }
    return Source;
  }
  if (!Dest)
    Dest = allocate(Source.Type, At);
  transfer(Source, Dest,
           Source.Expiring ? SpecialOperation::MoveConstruct
                           : SpecialOperation::CopyConstruct,
           At, false, CheckInvariant);
  return load({Source.Type, nullptr, Dest});
}

llvm::Value *Frame::resultAddress(const std::string &T, const Token &At) {
  if (!IR || !U.aggregate(T))
    return nullptr;
  if (ExpressionDestination.Address &&
      (ExpressionDestination.Type.empty() || ExpressionDestination.Type == T))
    return ExpressionDestination.Address;
  return allocate(T, At);
}
Value Frame::callResult(const std::string &T, llvm::Value *IRValue,
                        const Token &At, llvm::Value *Storage) {
  if (llvm::StringRef(T).ends_with("&")) {
    auto Base = T.substr(0, T.find_last_not_of('&') + 1);
    bool RO = llvm::StringRef(Base).starts_with("const<") && Base.back() == '>';
    Value Ref{RO ? Base.substr(6, Base.size() - 7) : Base, nullptr, IRValue,
              RO};
    Ref.Expiring = llvm::StringRef(T).ends_with("&&");
    return Ref;
  }
  auto Mutable = unconst(T);
  if (!Storage)
    return {Mutable, IRValue, nullptr, Mutable != T};
  auto V = load({Mutable, nullptr, Storage, Mutable != T});
  V.Expiring = V.Prvalue = true;
  if (Storage != ExpressionDestination.Address)
    Temps.push_back(V);
  return V;
}
