#include "Sema.h"
#include "llvm/ADT/MapVector.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/InstructionSimplify.h"
#include "llvm/Analysis/LazyValueInfo.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/OptimizationRemarkEmitter.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/PassInstrumentation.h"
#include "llvm/Transforms/Scalar/ConstraintElimination.h"
#include "llvm/Transforms/Scalar/EarlyCSE.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Utils/PromoteMemToReg.h"

using namespace cpn;

namespace {
llvm::CondBrInst *controllingBranch(llvm::BasicBlock *&Arm,
                                    llvm::BasicBlock &Join) {
  // An operand can have its own argument-evaluation blocks. Follow only an
  // unambiguous straight-line arm back to its conditional entry.
  for (unsigned Depth = 0; Depth < 32; ++Depth) {
    auto *Previous = Arm->getSinglePredecessor();
    if (!Previous || Previous == &Join)
      break;
    if (auto *Branch =
            llvm::dyn_cast<llvm::CondBrInst>(Previous->getTerminator()))
      return Branch;
    if (Previous->getSingleSuccessor() != Arm)
      break;
    Arm = Previous;
  }
  return nullptr;
}

llvm::Value *availableCondition(llvm::Value *V, llvm::IRBuilder<> &B,
                                llvm::DominatorTree &Dom, unsigned Depth = 0) {
  if (Dom.dominates(V, B.GetInsertPoint()))
    return V;
  if (Depth == 8)
    return nullptr;
  if (auto *Cast = llvm::dyn_cast<llvm::CastInst>(V);
      Cast && Cast->isIntegerCast()) {
    auto *Operand = availableCondition(Cast->getOperand(0), B, Dom, Depth + 1);
    return Operand ? B.CreateCast(Cast->getOpcode(), Operand, Cast->getType())
                   : nullptr;
  }
  if (auto *Compare = llvm::dyn_cast<llvm::ICmpInst>(V);
      Compare && Compare->getOperand(0)->getType()->isIntegerTy()) {
    auto *Left = availableCondition(Compare->getOperand(0), B, Dom, Depth + 1);
    auto *Right = availableCondition(Compare->getOperand(1), B, Dom, Depth + 1);
    if (Left && Right)
      return B.CreateICmp(Compare->getPredicate(), Left, Right);
  }
  return nullptr;
}

// Native short-circuit expressions have a Boolean join. Expose a simple join
// as a select without pruning edges, which might merge distinct failure sites.
// The select leaves an unused right operand outside the condition's value when
// the left operand bypassed it.
void exposeShortCircuitConditions(llvm::Function &F, llvm::DominatorTree &Dom) {
  for (auto &Block : F) {
    if (!Dom.isReachableFromEntry(&Block))
      continue;
    for (auto &Phi : llvm::make_early_inc_range(Block.phis())) {
      if (!Phi.getType()->isIntegerTy(1) || Phi.getNumIncomingValues() != 2)
        continue;
      auto *Shortcut =
          llvm::dyn_cast<llvm::ConstantInt>(Phi.getIncomingValue(0));
      unsigned Bypass = 0;
      if (!Shortcut) {
        Shortcut = llvm::dyn_cast<llvm::ConstantInt>(Phi.getIncomingValue(1));
        Bypass = 1;
      }
      if (!Shortcut)
        continue;
      auto *Skipped = Phi.getIncomingBlock(Bypass);
      auto *Evaluated = Phi.getIncomingBlock(1 - Bypass);
      if (Skipped->getSingleSuccessor() != &Block ||
          Evaluated->getSingleSuccessor() != &Block)
        continue;
      auto *Branch = controllingBranch(Skipped, Block);
      const unsigned BypassEdge = Shortcut->isOne() ? 0 : 1;
      if (!Branch || Branch != controllingBranch(Evaluated, Block) ||
          Branch->getSuccessor(BypassEdge) != Skipped ||
          Branch->getSuccessor(1 - BypassEdge) != Evaluated)
        continue;

      auto Insert = Block.getFirstNonPHIIt();
      llvm::IRBuilder<> B(Insert);
      auto *Right =
          availableCondition(Phi.getIncomingValue(1 - Bypass), B, Dom);
      if (!Right)
        continue;
      auto *Condition = B.CreateSelect(Branch->getCondition(),
                                       BypassEdge == 0 ? Shortcut : Right,
                                       BypassEdge == 0 ? Right : Shortcut);
      Phi.replaceAllUsesWith(Condition);
      Phi.eraseFromParent();
    }
  }
}

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
  Analyses.registerPass([] { return llvm::LoopAnalysis(); });
  Analyses.registerPass(
      [] { return llvm::OptimizationRemarkEmitterAnalysis(); });
  Analyses.registerPass([] { return llvm::ScalarEvolutionAnalysis(); });
  Analyses.registerPass([&] {
    llvm::TargetLibraryInfoImpl Library(F.getParent()->getTargetTriple());
    Library.disableAllFunctions();
    return llvm::TargetLibraryAnalysis(Library);
  });
  Analyses.registerPass([] { return llvm::TargetIRAnalysis(); });
  Analyses.invalidate(F, llvm::EarlyCSEPass().run(F, Analyses));
  exposeShortCircuitConditions(
      F, Analyses.getResult<llvm::DominatorTreeAnalysis>(F));

  const auto Query = llvm::SimplifyQuery(F.getDataLayout()).getWithoutUndef();
  bool Changed;
  do {
    // Keep relations between SSA inputs along dominating edges. A range for
    // either input alone cannot prove, for example, a < c from a < b <= c.
    Analyses.invalidate(F, llvm::ConstraintEliminationPass().run(F, Analyses));
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
    if (Changed)
      Analyses.invalidate(F, llvm::PreservedAnalyses::none());
  } while (Changed);
}
} // namespace

bool Context::proveNoContractFailure(llvm::Function &F) {
  // Implication is over valid boundary states. Readiness instrumentation
  // cannot modify any source object while evaluating the predicates.
  for (auto &Block : F)
    for (auto &Inst : llvm::make_early_inc_range(Block))
      if (auto *Call = llvm::dyn_cast<llvm::CallInst>(&Inst);
          Call && StaticRead && Call->getCalledFunction() == StaticRead)
        Call->eraseFromParent();
  reduceProofCFG(F);
  for (const auto &Block : F)
    for (const auto &Inst : Block)
      if (Inst.getMetadata("cpn.override.failure"))
        return false;
  return true;
}

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
