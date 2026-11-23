#include "Sema.h"

using namespace cpn;

llvm::Function *Context::foreignContractEntry(Function &D) {
  const auto &Policy = D.Defaults.Configuration;
  if (!D.Decl.Foreign || !D.Decl.Prototype || D.Decl.Contracts.empty() ||
      !Policy.ContractsEnabled ||
      (Policy.ContractValidation != "check" &&
       Policy.ContractValidation != "prove"))
    return D.IR;

  if (!D.ImportAdapter) {
    D.ImportAdapter = llvm::Function::Create(D.IR->getFunctionType(),
                                             llvm::GlobalValue::PrivateLinkage,
                                             "cpn.checked_import." + D.Name, M);
    D.ImportAdapter->setCallingConv(D.IR->getCallingConv());
    D.ImportAdapter->setAttributes(D.IR->getAttributes());
  }
  return D.ImportAdapter;
}

void Context::emitForeignContractAdapters() {
  for (size_t I = 0; I < Functions.size(); ++I) {
    auto &D = Functions[I];
    auto *Entry = D.ImportAdapter;
    if (!Entry)
      continue;
    // A later definition in this unit checks its own contract at the C entry.
    if (!D.Decl.Prototype || Entry->use_empty()) {
      Entry->replaceAllUsesWith(D.IR);
      Entry->eraseFromParent();
      D.ImportAdapter = nullptr;
      continue;
    }

    Frame F(*this, &D, Entry);
    F.B.SetInsertPoint(F.block("entry"));
    F.bindParams();
    F.checkContracts(true);

    llvm::SmallVector<llvm::Value *> Arguments;
    for (auto &Argument : Entry->args())
      Arguments.push_back(&Argument);
    auto *Call = F.B.CreateCall(D.IR, Arguments);
    Call->setCallingConv(D.IR->getCallingConv());
    Call->setAttributes(D.IR->getAttributes());

    Value Result{D.Result, Call};
    F.checkContracts(false, Result);
    F.cleanup(0);
    F.publishPointerResult(Result);
    if (D.Result == "void")
      F.B.CreateRetVoid();
    else
      F.B.CreateRet(Call);
  }
}
