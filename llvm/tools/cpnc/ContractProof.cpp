#include "Sema.h"
#include "llvm/ADT/MapVector.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/InstructionSimplify.h"
#include "llvm/Analysis/LazyValueInfo.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/PassInstrumentation.h"
#include "llvm/Transforms/Scalar/EarlyCSE.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Utils/PromoteMemToReg.h"

using namespace cpn;

namespace {
void reduceProofCFG(llvm::Function &F) {
  llvm::SmallVector<llvm::AllocaInst *> Locals;
  for (auto &Inst : F.getEntryBlock())
    if (auto *Slot = llvm::dyn_cast<llvm::AllocaInst>(&Inst);
        Slot && llvm::isAllocaPromotable(Slot))
      Locals.push_back(Slot);
  if (!Locals.empty()) {
    llvm::DominatorTree Dom(F);
    llvm::PromoteMemToReg(Locals, Dom);
  }
  llvm::FunctionAnalysisManager Analyses;
  Analyses.registerPass([] { return llvm::PassInstrumentationAnalysis(); });
  Analyses.registerPass([] { return llvm::AssumptionAnalysis(); });
  Analyses.registerPass([] { return llvm::DominatorTreeAnalysis(); });
  Analyses.registerPass([&] {
    llvm::TargetLibraryInfoImpl Library(F.getParent()->getTargetTriple());
    Library.disableAllFunctions();
    return llvm::TargetLibraryAnalysis(Library);
  });
  Analyses.registerPass([] { return llvm::TargetIRAnalysis(); });
  llvm::EarlyCSEPass().run(F, Analyses);

  const auto Query = llvm::SimplifyQuery(F.getDataLayout()).getWithoutUndef();
  bool Changed;
  do {
    Changed = false;
    for (auto &Block : F)
      for (auto &Inst : llvm::make_early_inc_range(Block))
        if (!Inst.use_empty())
          if (auto *Replacement = llvm::simplifyInstruction(&Inst, Query);
              Replacement && Replacement != &Inst) {
            Inst.replaceAllUsesWith(Replacement);
            if (llvm::isInstructionTriviallyDead(&Inst))
              Inst.eraseFromParent();
            Changed = true;
          }

    llvm::AssumptionCache Assumptions(F);
    llvm::LazyValueInfo Values(&F, &Assumptions);
    llvm::SmallVector<std::pair<llvm::CondBrInst *, llvm::ConstantInt *>> Known;
    for (auto &Block : F) {
      auto *Branch = llvm::dyn_cast<llvm::CondBrInst>(Block.getTerminator());
      if (!Branch)
        continue;
      auto *Value = Branch->getCondition();
      auto *Fixed = Values.getConstant(Value, Branch);
      if (!Fixed)
        if (auto *Compare = llvm::dyn_cast<llvm::ICmpInst>(Value))
          Fixed = Values.getPredicateAt(Compare->getPredicate(),
                                        Compare->getOperand(0),
                                        Compare->getOperand(1), Branch, true);
      if (auto *Constant = llvm::dyn_cast_or_null<llvm::ConstantInt>(Fixed))
        Known.emplace_back(Branch, Constant);
    }
    Values.releaseMemory();
    for (auto [Branch, Constant] : Known)
      Branch->setCondition(Constant);
    for (auto &Block : F)
      Changed |= llvm::ConstantFoldTerminator(&Block, true);
    Changed |= llvm::removeUnreachableBlocks(F, nullptr, nullptr, false);
  } while (Changed);
}
} // namespace

void Context::verifyProvenContracts() {
  if (ContractProofs.empty())
    return;
  llvm::MapVector<llvm::Function *, std::vector<const ContractProof *>>
      ByFunction;
  for (const auto &[Index, Proof] : llvm::enumerate(ContractProofs)) {
    ByFunction[Proof.Before->getParent()].push_back(&Proof);
    auto *ID = llvm::ConstantAsMetadata::get(
        llvm::ConstantInt::get(llvm::Type::getInt64Ty(C), Index));
    Proof.Failure->front().setMetadata("cpn.proof", llvm::MDNode::get(C, ID));
  }

  // Obtain evidence in a scratch CFG. No optimizer transformations from the
  // proof pass are applied to the source function's observable operations.
  auto Scratch = llvm::CloneModule(M);
  std::vector<bool> Unproved(ContractProofs.size(), false);
  for (const auto &[Source, Proofs] : ByFunction) {
    auto &Function = *Scratch->getFunction(Source->getName());
    reduceProofCFG(Function);
    for (const auto &Block : Function)
      for (const auto &Inst : Block)
        if (const auto *Proof = Inst.getMetadata("cpn.proof"))
          Unproved[llvm::mdconst::extract<llvm::ConstantInt>(
                       Proof->getOperand(0))
                       ->getZExtValue()] = true;
  }
  for (auto [Index, Proof] : llvm::enumerate(ContractProofs))
    if (Unproved[Index])
      fail(Proof.At, "cannot establish " + Proof.Label);

  for (const auto &[Source, Proofs] : ByFunction) {
    for (const auto *Proof : Proofs) {
      auto *ToPredicate = Proof->Before->getTerminator();
      auto *Entry = ToPredicate->getSuccessor(0);
      Entry->removePredecessor(Proof->Before);
      ToPredicate->setSuccessor(0, Proof->Success);
    }
    llvm::removeUnreachableBlocks(*Source, nullptr, nullptr, false);
  }
  ContractProofs.clear();
}
