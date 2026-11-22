#include "Sema.h"
using namespace cpn;

bool Frame::usesStorage(const Node &N) {
  if (N.K == Node::Call && !N.Children.empty() &&
      N.Children[0].K == Node::Name) {
    auto &S = N.Children[0].Text;
    if (S == "storage_of" || S == "destroy" || S == "abandon" ||
        S == "construct_at")
      return true;
  }
  return llvm::any_of(N.Children, [](const Node &C) { return usesStorage(C); });
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
void Frame::track(Value &V) {
  if (!TracksStorage)
    return;
  auto *S = allocate("u64", {}), *D = allocate("void*", {});
  auto *Drop = U.cleanupEntry(V.Type);
  B.CreateStore(Drop ? static_cast<llvm::Constant *>(Drop)
                     : llvm::ConstantPointerNull::get(B.getPtrTy()),
                D);
  B.CreateStore(B.getInt64(1), S);
  V.Generation = B.getInt64(1);
  Registrations[V.Storage] = {S, D};
}
void Frame::ensureLive(const Value &V, const Token &At) {
  if (V.Storage.empty() || !Active.count(V.Storage))
    return;
  if (Active.at(V.Storage) == 0)
    fail(At, "ended object generation");
  auto I = Registrations.find(V.Storage);
  if (I == Registrations.end())
    return;
  auto *Stamp = B.CreateLoad(B.getInt64Ty(), I->second.Stamp);
  if (V.Generation)
    guard(B.CreateICmpNE(V.Generation, Stamp));
  else if (Active.at(V.Storage) < 0)
    guard(B.CreateNot(B.CreateTrunc(Stamp, B.getInt1Ty())));
}
void Frame::retireStorage(const Value &V, bool Destroy) {
  auto I = Registrations.find(V.Storage);
  if (I == Registrations.end()) {
    if (Destroy) {
      auto Bare = V;
      Bare.Storage.clear();
      drop(Bare);
    }
    Active[V.Storage] = 0;
    return;
  }
  auto &R = I->second;
  auto *Stamp = B.CreateLoad(B.getInt64Ty(), R.Stamp);
  auto *Live = B.CreateTrunc(Stamp, B.getInt1Ty());
  auto *Retire = block("storage.retire"), *Done = block("storage.done");
  B.CreateCondBr(Live, Retire, Done);
  B.SetInsertPoint(Retire);
  B.CreateStore(B.CreateAdd(Stamp, B.getInt64(1)), R.Stamp);
  if (Destroy) {
    auto *Drop = B.CreateLoad(B.getPtrTy(), R.Destructor);
    auto *Call = block("storage.drop");
    B.CreateCondBr(B.CreateIsNotNull(Drop), Call, Done);
    B.SetInsertPoint(Call);
    auto *FT = llvm::FunctionType::get(B.getVoidTy(), {B.getPtrTy()}, false);
    B.CreateCall(FT, Drop, {Extents.at(V.Storage).Address});
  }
  branch(Done);
  B.SetInsertPoint(Done);
  Active[V.Storage] = 0;
}
void Frame::replaceGeneration(const Value &S, const std::string &T,
                              const Token &At) {
  if (!Registrations.count(S.Storage))
    fail(At, "local storage registration required");
  auto &R = Registrations.at(S.Storage);
  auto *Drop = U.cleanupEntry(T);
  B.CreateStore(Drop ? static_cast<llvm::Constant *>(Drop)
                     : llvm::ConstantPointerNull::get(B.getPtrTy()),
                R.Destructor);
  B.CreateStore(
      B.CreateAdd(B.CreateLoad(B.getInt64Ty(), R.Stamp), B.getInt64(1)),
      R.Stamp);
  Active[S.Storage] = 1;
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
