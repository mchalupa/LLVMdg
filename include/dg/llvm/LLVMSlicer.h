#ifndef LLVM_DG_SLICER_H_
#define LLVM_DG_SLICER_H_

#include <llvm/Config/llvm-config.h>
#include <llvm/IR/Module.h>
#if ((LLVM_VERSION_MAJOR == 3) && (LLVM_VERSION_MINOR < 5))
#include <llvm/Support/CFG.h>
#else
#include <llvm/IR/CFG.h>
#endif

#include <llvm/IR/Constants.h>
#include <llvm/IR/GlobalVariable.h>
#include <llvm/IR/Instruction.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Value.h>
#include <llvm/Support/raw_ostream.h>

#include "dg/Slicing.h"
#include "dg/llvm/LLVMDependenceGraph.h"
#include "dg/llvm/LLVMNode.h"

namespace dg {

class LLVMNode;

extern std::map<const llvm::Value *, LLVMDependenceGraph *>
        constructedFunctions;

namespace llvmdg {

template <typename Val>
static void dropAllUses(Val *V) {
    for (auto I = V->use_begin(), E = V->use_end(); I != E; ++I) {
#if ((LLVM_VERSION_MAJOR == 3) && (LLVM_VERSION_MINOR < 5))
        llvm::Value *use = *I;
#else
        llvm::Value *use = I->getUser();
#endif

        // drop the reference to this value
        llvm::cast<llvm::Instruction>(use)->replaceUsesOfWith(V, nullptr);
    }
}

class LLVMSlicer : public Slicer<LLVMNode> {
  public:
    LLVMSlicer() = default;

    void keepFunctionUntouched(const char *n) { dont_touch.insert(n); }

    bool removeNode(LLVMNode *node) override {
        using namespace llvm;

        Value *val = node->getKey();
        // if there are any other uses of this value,
        // just replace them with undef
        val->replaceAllUsesWith(UndefValue::get(val->getType()));

        Instruction *Inst = dyn_cast<Instruction>(val);
        if (Inst) {
            Inst->eraseFromParent();
        } else {
            GlobalVariable *GV = dyn_cast<GlobalVariable>(val);
            if (GV)
                GV->eraseFromParent();
        }

        return true;
    }

    bool removeBlock(LLVMBBlock *block) override {
        assert(block);

        llvm::Value *val = block->getKey();
        if (val == nullptr)
            return true;

        llvm::BasicBlock *blk = llvm::cast<llvm::BasicBlock>(val);
        for (const auto &succ : block->successors()) {
            if (succ.label == LLVMBBlock::ARTIFICIAL_BBLOCK_LABEL)
                continue;

            // don't adjust phi nodes in this block if this is a self-loop,
            // we're gonna remove the block anyway
            if (succ.target == block)
                continue;

            if (llvm::Value *sval = succ.target->getKey())
                adjustPhiNodes(llvm::cast<llvm::BasicBlock>(sval), blk);
        }

        // We need to drop the reference to this block in all
        // braching instructions that jump to this block.
        // See #99
        dropAllUses(blk);

        // we also must drop refrences to instructions that are in
        // this block (or we would need to delete the blocks in
        // post-dominator order), see #101
        for (llvm::Instruction &Inst : *blk)
            dropAllUses(&Inst);

        // finally, erase the block per se
        blk->eraseFromParent();
        return true;
    }

    // override slice method
    static uint32_t slice(LLVMNode *start, uint32_t sl_id = 0) {
        (void) sl_id;
        (void) start;

        assert(0 && "Do not use this method with LLVM dg");
        return 0;
    }

    uint32_t slice(LLVMDependenceGraph *dg, LLVMNode *start,
                   uint32_t sl_id = 0) {
        // mark nodes for slicing
        assert(start || sl_id != 0);
        if (start)
            sl_id = mark(start, sl_id);

        std::vector<llvm::Function *> to_erase;
        for (auto &F : *dg->getModule()) {
            if (dontTouch(F.getName()))
                continue;

            auto it = constructedFunctions.find(&F);
            if (it == constructedFunctions.end()) {
                // remove (defined) functions that we didn't even constructed,
                // those are irrelevant in the slice
                if (!F.isDeclaration()) {
                    to_erase.push_back(&F);
                }
            } else {
                LLVMDependenceGraph *subdg = it->second;
                sliceGraph(subdg, sl_id);
            }
        }
        for (auto *F : to_erase) {
            F->replaceAllUsesWith(llvm::UndefValue::get(F->getType()));
            F->deleteBody();
            F->eraseFromParent();
        }

        return sl_id;
    }

  private:
    /*
void sliceCallNode(LLVMNode *callNode,
                   LLVMDependenceGraph *graph, uint32_t slice_id)
{
    LLVMDGParameters *actualparams = callNode->getParameters();
    LLVMDGParameters *formalparams = graph->getParameters();

    if (!actualparams) {
        assert(!formalparams && "Have only one of params");
        return; // no params - nothing to do
    }

    assert(formalparams && "Have only one of params");
    assert(formalparams->size() == actualparams->size());

    // FIXME slice arguments away
}

void sliceCallNode(LLVMNode *callNode, uint32_t slice_id)
{
    for (LLVMDependenceGraph *subgraph : callNode->getSubgraphs())
        sliceCallNode(callNode, subgraph, slice_id);
}
    */

    static void adjustPhiNodes(llvm::BasicBlock *pred, llvm::BasicBlock *blk) {
        using namespace llvm;

        for (Instruction &I : *pred) {
            PHINode *phi = dyn_cast<PHINode>(&I);
            if (phi) {
                // don't try remove block that we already removed
                int idx = phi->getBasicBlockIndex(blk);
                if (idx < 0)
                    continue;

                // the second argument is DeletePHIIFEmpty.
                // We don't want that, since that would make
                // dependence graph inconsistent. We'll
                // slice it away later, if it's empty
                phi->removeIncomingValue(idx, false);
            } else {
                // phi nodes are always at the beginning of the block
                // so if this is the first value that is not PHI,
                // there won't be any other and we can bail out
                break;
            }
        }
    }

    static inline bool shouldSliceInst(const llvm::Value *val) {
        using namespace llvm;
        const Instruction *Inst = dyn_cast<Instruction>(val);
        if (!Inst)
            return true;

        switch (Inst->getOpcode()) {
        case Instruction::Unreachable:
#if 0
            case Instruction::Br:
            case Instruction::Switch:
            case Instruction::Ret:
#endif
            return false;
        default:
            return true;
        }
    }

    static LLVMBBlock *createNewExitBB(LLVMDependenceGraph *graph) {
        using namespace llvm;

        LLVMBBlock *exitBB = new LLVMBBlock();

        Module *M = graph->getModule();
        LLVMContext &Ctx = M->getContext();
        BasicBlock *block = BasicBlock::Create(Ctx, "safe_return");

        Value *fval = graph->getEntry()->getKey();
        Function *F = cast<Function>(fval);
        F->insert(F->end(), block);

        // fill in basic block just with return value
        ReturnInst *RI;
        if (F->getReturnType()->isVoidTy())
            RI = ReturnInst::Create(Ctx, block);
        else if (F->getName().equals("main"))
            // if this is main, than the safe exit equals to returning 0
            // (it is just for convenience, we wouldn't need to do this)
            RI = ReturnInst::Create(
                    Ctx, ConstantInt::get(Type::getInt32Ty(Ctx), 0), block);
        else
            RI = ReturnInst::Create(Ctx, UndefValue::get(F->getReturnType()),
                                    block);

        LLVMNode *newRet = new LLVMNode(RI);
        graph->addNode(newRet);

        exitBB->append(newRet);
        exitBB->setKey(block);
        exitBB->setDG(graph);

        return exitBB;
    }

    static LLVMBBlock *addNewExitBB(LLVMDependenceGraph *graph) {
        // FIXME: don't create new one, create it
        // when creating graph and just use that one
        LLVMBBlock *newExitBB = createNewExitBB(graph);
        graph->setExitBB(newExitBB);
        graph->setExit(newExitBB->getLastNode());
        // do not add the block to the graph,
        // we'll do it at the end of adjustBBlocksSucessors,
        // because this function is called while iterating
        // over blocks, so that we won't corrupt the iterator

        return newExitBB;
    }

    // when we sliced away a branch of CFG, we need to reconnect it
    // to exit block, since on this path we would silently terminate
    // (this path won't have any effect on the property anymore)
    static void adjustBBlocksSucessors(LLVMDependenceGraph *graph,
                                       uint32_t slice_id) {
        LLVMBBlock *oldExitBB = graph->getExitBB();
        assert(oldExitBB && "Don't have exit BB");

        LLVMBBlock *newExitBB = nullptr;

        for (auto &it : graph->getBlocks()) {
            const llvm::BasicBlock *llvmBB =
                    llvm::cast<llvm::BasicBlock>(it.first);
            const auto *const tinst = llvmBB->getTerminator();
            LLVMBBlock *BB = it.second;

            // nothing to do
            if (BB->successorsNum() == 0)
                continue;

            // if the BB has two successors and one is self-loop and
            // the branch inst is going to be removed, then the brach
            // that created the self-loop has no meaning to the sliced
            // program and this is going to be an unconditional jump
            // to the other branch
            // NOTE: do this before the next action, to rename the label if
            // needed
            if (BB->successorsNum() == 2 &&
                BB->getLastNode()->getSlice() != slice_id &&
                !BB->successorsAreSame() && BB->hasSuccessor(BB)) {
                bool found = BB->removeSuccessorsTarget(BB);
                // we have two different successors, none of them
                // is self-loop and we're slicing away the brach inst?
                // This should not happen...
                if (!found) {
                    assert(found && "Self loop did not have self loop...");
                    abort();
                }
                assert(BB->successorsNum() == 1 &&
                       "Should have only one successor");

                // continue here to rename the only label if needed
            }

            // if the BB has only one successor and the terminator
            // instruction is going to be sliced away, it means that
            // this is going to be an unconditional jump,
            // so just make the label 0
            if (BB->successorsNum() == 1 &&
                BB->getLastNode()->getSlice() != slice_id) {
                auto edge = *(BB->successors().begin());

                // modify the edge
                edge.label = 0;
                if (edge.target == oldExitBB) {
                    if (!newExitBB)
                        newExitBB = addNewExitBB(graph);

                    edge.target = newExitBB;
                }

                // replace the only edge
                BB->removeSuccessors();
                BB->addSuccessor(edge);

                continue;
            }

            // when we have more successors, we need to fill in
            // jumps under labels that we sliced away

            DGContainer<uint8_t> labels;
            // go through BBs successors and gather all labels
            // from edges that go from this BB. Also if there's
            // a jump to return block, replace it with new
            // return block
            for (const auto &succ : BB->successors()) {
                // skip artificial return basic block.
                if (succ.label == LLVMBBlock::ARTIFICIAL_BBLOCK_LABEL ||
                    succ.target == oldExitBB)
                    continue;

                labels.insert(succ.label);
            }

            // replace missing labels. Label should be from 0 to some max,
            // no gaps, so jump to safe exit under missing labels
            for (unsigned i = 0; i < tinst->getNumSuccessors(); ++i) {
                if (!labels.contains(i)) {
                    if (!newExitBB)
                        newExitBB = addNewExitBB(graph);

#ifndef NDEBUG
                    bool ret =
#endif
                            BB->addSuccessor(newExitBB, i);
                    assert(ret && "Already had this CFG edge, that is wrong");
                }
            }

            // this BB is going to be removed
            if (newExitBB)
                BB->removeSuccessorsTarget(oldExitBB);

            // if we have all successor edges pointing to the same
            // block, replace them with one successor (thus making
            // unconditional jump)
            if (BB->successorsNum() > 1 && BB->successorsAreSame()) {
                LLVMBBlock *succ = BB->successors().begin()->target;

                BB->removeSuccessors();
                BB->addSuccessor(succ, 0);
#ifdef NDEBUG
                assert(BB->successorsNum() == 1 &&
                       "BUG: in removeSuccessors() or addSuccessor()");
#endif
            }

#ifndef NDEBUG
            // check the BB
            labels.clear();
            for (const auto &succ : BB->successors()) {
                assert((!newExitBB || succ.target != oldExitBB) &&
                       "A block has the old BB as successor");
                // we can have more labels with different targets,
                // but we can not have one target with more labels
                assert(labels.insert(succ.label) && "Already have a label");
            }

            // check that we have all labels without any gep
            auto l = labels.begin();
            for (unsigned i = 0; i < labels.size(); ++i) {
                // set is ordered, so this must hold
                assert((*l == LLVMBBlock::MAX_BBLOCK_LABEL || i == *l++) &&
                       "Labels have a gap");
            }
#endif
        }

        if (newExitBB) {
            graph->addBlock(newExitBB->getKey(), newExitBB);
            assert(graph->getExitBB() == newExitBB);
            // NOTE: do not delete the old block
            // because it is the unified BB that is kept in
            // unique_ptr, so it will be deleted later automatically.
            // Deleting it would lead to double-free
        }
    }

    void sliceGraph(LLVMDependenceGraph *graph, uint32_t slice_id) {
        // first slice away bblocks that should go away
        sliceBBlocks(graph, slice_id);

        // make graph complete
        adjustBBlocksSucessors(graph, slice_id);

        // now slice away instructions from BBlocks that left
        for (auto I = graph->begin(), E = graph->end(); I != E;) {
            LLVMNode *n = I->second;
            // shift here, so that we won't corrupt the iterator
            // by deleteing the node
            ++I;

            // we added this node artificially and
            // we don't want to slice it away or
            // take any other action on it
            if (n == graph->getExit())
                continue;

            ++statistics.nodesTotal;

            // keep instructions like ret or unreachable
            // FIXME: if this is ret of some value, then
            // the value is undef now, so we should
            // replace it by void ref
            if (!shouldSliceInst(n->getKey()))
                continue;

            /*
            if (llvm::isa<llvm::CallInst>(n->getKey()))
                sliceCallNode(n, slice_id);
                */

            if (n->getSlice() != slice_id) {
                removeNode(n);
                graph->deleteNode(n);
                ++statistics.nodesRemoved;
            }
        }

        // create new CFG edges between blocks after slicing
        reconnectLLLVMBasicBlocks(graph);

        // if we sliced away entry block, our new entry block
        // may have predecessors, which is not allowed in the
        // LLVM
        ensureEntryBlock(graph);
    }

    bool dontTouch(const llvm::StringRef &r) {
        for (const char *n : dont_touch)
            if (r.equals(n))
                return true;

        return false;
    }

    static void reconnectBBlock(LLVMBBlock *BB, llvm::BasicBlock *llvmBB) {
        using namespace llvm;

        auto *tinst = llvmBB->getTerminator();
        assert((!tinst || BB->successorsNum() <= 2 ||
                llvm::isa<llvm::SwitchInst>(tinst)) &&
               "BB has more than two successors (and it's not a switch)");

        if (!tinst) {
            // block has no terminator
            // It may occur for example if we have:
            //
            //   call error()
            //   br %exit
            //
            //  The br instruction has no meaning when error() abort,
            //  but if error is not marked as noreturn, then the br
            //  will be there and will get sliced, making the block
            //  unterminated. The same may happen if we remove unconditional
            //  branch inst

            LLVMContext &Ctx = llvmBB->getContext();
            Function *F = cast<Function>(llvmBB->getParent());
            bool create_return = true;

            if (BB->successorsNum() == 1) {
                const LLVMBBlock::BBlockEdge &edge =
                        *(BB->successors().begin());
                if (edge.label != LLVMBBlock::ARTIFICIAL_BBLOCK_LABEL) {
                    // don't create return, we created branchinst
                    create_return = false;

                    BasicBlock *succ = cast<BasicBlock>(edge.target->getKey());
                    BranchInst::Create(succ, llvmBB);
                }
            }

            if (create_return) {
                if (BB->successorsNum() != 0) {
                    assert(BB->successorsNum() == 0 &&
                           "Creating return to BBlock that has successors");
                    abort();
                }

                if (F->getReturnType()->isVoidTy())
                    ReturnInst::Create(Ctx, llvmBB);
                else if (F->getName().equals("main"))
                    // if this is main, than the safe exit equals to returning 0
                    // (it is just for convenience, we wouldn't need to do this)
                    ReturnInst::Create(
                            Ctx, ConstantInt::get(Type::getInt32Ty(Ctx), 0),
                            llvmBB);
                else
                    ReturnInst::Create(Ctx, UndefValue::get(F->getReturnType()),
                                       llvmBB);
            }

            // and that is all we can do here
            return;
        }

        for (const LLVMBBlock::BBlockEdge &succ : BB->successors()) {
            // skip artificial return basic block
            if (succ.label == LLVMBBlock::ARTIFICIAL_BBLOCK_LABEL)
                continue;

            llvm::Value *val = succ.target->getKey();
            assert(val && "nullptr as BB's key");
            llvm::BasicBlock *llvmSucc = llvm::cast<llvm::BasicBlock>(val);
            tinst->setSuccessor(succ.label, llvmSucc);
        }

        // if the block still does not have terminator
    }

    static void reconnectLLLVMBasicBlocks(LLVMDependenceGraph *graph) {
        for (auto &it : graph->getBlocks()) {
            llvm::BasicBlock *llvmBB = llvm::cast<llvm::BasicBlock>(it.first);
            LLVMBBlock *BB = it.second;

            reconnectBBlock(BB, llvmBB);
        }
    }

    static void ensureEntryBlock(LLVMDependenceGraph *graph) {
        using namespace llvm;

        Value *val = graph->getEntry()->getKey();
        Function *F = cast<Function>(val);

        // Function is empty, just bail out
        if (F->begin() == F->end())
            return;

        BasicBlock *entryBlock = &F->getEntryBlock();

        if (pred_begin(entryBlock) == pred_end(entryBlock)) {
            // entry block has no predecessor, we're ok
            return;
        }

        // it has some predecessor, create new one, that will just
        // jump on it
        LLVMContext &Ctx = graph->getModule()->getContext();
        BasicBlock *block = BasicBlock::Create(Ctx, "single_entry");

        // jump to the old entry block
        BranchInst::Create(entryBlock, block);

        // set it as a new entry by pusing the block to the front
        // of the list
        F->insert(F->begin(), block);

        // FIXME: propagate this change to dependence graph
    }

    // do not slice these functions at all
    std::set<const char *> dont_touch;
};

} // namespace llvmdg
} // namespace dg

#endif
