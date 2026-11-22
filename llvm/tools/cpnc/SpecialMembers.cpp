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
  if (llvm::StringRef(T).ends_with("]"))
    return constructible(element(T), Op, At);
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
  return llvm::all_of(
      R.Fields, [&](auto &Field) { return constructible(Field.Type, Op, At); });
}
void Frame::transfer(Value Source, llvm::Value *Dest, SpecialOperation Op,
                     const Token &At) {
  auto *Ty = U.ir(Source.Type, At);
  if (auto *Array = llvm::dyn_cast<llvm::ArrayType>(Ty)) {
    // Evaluate aggregate designators once. Each element's own declared
    // operation executes before continuing to the next element.
    auto Elem = element(Source.Type);
    if (U.Records.count(Elem) ||
        llvm::isa<llvm::ArrayType>(Array->getElementType())) {
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
      Index->addIncoming(Next, B.GetInsertBlock());
      B.CreateCondBr(B.CreateICmpULT(Next, B.getInt64(Array->getNumElements())),
                     Loop, Done);
      B.SetInsertPoint(Done);
      return;
    }
  }
  auto It = U.Records.find(Source.Type);
  if (It == U.Records.end()) {
    B.CreateStore(load(Source).IR, Dest);
    return;
  }
  auto &R = It->second;
  Value Result{Source.Type, nullptr, Dest};
  if (moving(Op) && Source.Readonly)
    fail(At, "moving requires a mutable source");
  if (R.Decl.K != Node::Lambda) {
    auto I = R.Special.find(Op);
    if (I == R.Special.end())
      fail(At, std::string("no available ") + operationName(Op) + " for " +
                   Source.Type);
    auto &Member = I->second;
    checkAccess(Member.Decl, Source.Type, At);
    if (Member.Decl.Settings.count("control") &&
        Member.Decl.Settings.at("control") == "delete")
      fail(At, std::string("selected ") + operationName(Op) + " is deleted");
    if (Member.Body) {
      Source.Expiring = moving(Op);
      invoke(*Member.Body, {Source}, At, Result);
      return;
    }
  }
  if (!assignment(Op))
    B.CreateStore(llvm::Constant::getNullValue(Ty), Dest);
  for (size_t I = 0; I < R.Fields.size(); ++I) {
    auto &Field = R.Fields[I];
    auto *From = B.CreateStructGEP(R.IR, Source.Address, I);
    auto *To = B.CreateStructGEP(R.IR, Dest, I);
    transfer({Field.Type, nullptr, From, Source.Readonly}, To, Op, At);
  }
  if (!assignment(Op))
    installTables(Result);
}

Value Frame::materialize(Value Source, const Token &At, llvm::Value *Dest) {
  bool Aggregate = U.Records.count(Source.Type) ||
                   llvm::StringRef(Source.Type).ends_with("]");
  if (!Aggregate || !Source.Address || Source.Prvalue) {
    if (Source.Prvalue)
      consume(Source);
    if (Dest)
      B.CreateStore(load(Source).IR, Dest);
    return Source;
  }
  if (!Dest)
    Dest = allocate(Source.Type, At);
  transfer(Source, Dest,
           Source.Expiring ? SpecialOperation::MoveConstruct
                           : SpecialOperation::CopyConstruct,
           At);
  return {Source.Type, B.CreateLoad(U.ir(Source.Type, At), Dest), Dest};
}

Value Frame::callResult(const std::string &T, llvm::Value *IRValue,
                        const Token &At) {
  if (llvm::StringRef(T).ends_with("&")) {
    auto Base = T.substr(0, T.find_last_not_of('&') + 1);
    bool RO = llvm::StringRef(Base).starts_with("const<") && Base.back() == '>';
    Value Ref{RO ? Base.substr(6, Base.size() - 7) : Base, nullptr, IRValue,
              RO};
    Ref.Expiring = llvm::StringRef(T).ends_with("&&");
    return load(Ref);
  }
  if (!U.Records.count(T) && !llvm::StringRef(T).ends_with("]"))
    return {T, IRValue};
  auto *Ptr = allocate(T, At);
  B.CreateStore(IRValue, Ptr);
  Value V{T, IRValue, Ptr};
  V.Expiring = V.Prvalue = true;
  Temps.push_back(V);
  return V;
}
