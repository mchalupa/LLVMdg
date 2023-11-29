#include <cassert>
#include <set>

#include <llvm/Config/llvm-config.h>

#if ((LLVM_VERSION_MAJOR == 3) && (LLVM_VERSION_MINOR < 5))
#include <llvm/Support/CFG.h>
#else
#include <llvm/IR/CFG.h>
#endif

#include <llvm/IR/Constant.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/DataLayout.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instruction.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/Module.h>
#include <llvm/Support/raw_os_ostream.h>

#include "dg/llvm/PointerAnalysis/PointerGraph.h"
#include "dg/util/debug.h"

namespace dg {
namespace pta {

void LLVMPointerGraphBuilder::FuncGraph::blockAddSuccessors(
        std::set<const llvm::BasicBlock *> &found_blocks,
        LLVMPointerGraphBuilder::PSNodesBlock &blk,
        const llvm::BasicBlock &block) {
    for (auto S = llvm::succ_begin(&block), SE = llvm::succ_end(&block);
         S != SE; ++S) {
        // we already processed this block? Then don't try to add the edges
        // again
        if (!found_blocks.insert(*S).second)
            continue;

        auto it = llvmBlocks.find(*S);
        if (it == llvmBlocks.end()) {
            // if we don't have this block built (there was no points-to
            // relevant instruction), we must pretend to be there for
            // control flow information. Thus instead of adding it as
            // successor, add its successors as successors
            blockAddSuccessors(found_blocks, blk, *(*S));
        } else {
            // add successor to the last nodes
            blk.getLastNode()->addSuccessor(it->second.getFirstNode());
        }
    }
}

LLVMPointerGraphBuilder::PSNodesBlock
LLVMPointerGraphBuilder::buildArgumentsStructure(const llvm::Function &F) {
    PSNodesBlock blk;

    int idx = 0;
    for (auto A = F.arg_begin(), E = F.arg_end(); A != E; ++A, ++idx) {
        auto it = nodes_map.find(&*A);
        if (it == nodes_map.end())
            continue;

        PSNodesSeq &cur = it->second;
        assert(cur.getFirst() == cur.getLast());

        blk.append(&cur);
    }

    // add CFG edges between the arguments
    PSNodesBlockAddSuccessors(blk);

    return blk;
}

void LLVMPointerGraphBuilder::addProgramStructure(const llvm::Function *F,
                                                  PointerSubgraph &subg) {
    assert(subg.root && "Subgraph has no root");

    assert(_funcInfo.find(F) != _funcInfo.end());
    auto &finfo = _funcInfo[F];

    // with function pointer calls it may happen that we try
    // to add structure more times, so bail out in that case
    if (finfo.has_structure) {
        DBG(pta, "Already got structure for function '" << F->getName().str()
                                                        << "', bailing out");
        return;
    }

    PSNodesBlock argsBlk = buildArgumentsStructure(*F);
    PSNode *lastNode = connectArguments(F, argsBlk, subg);
    assert(lastNode && "Did not connect arguments of a function correctly");

    // add successors in each one basic block
    for (auto &it : finfo.llvmBlocks) {
        PSNodesBlockAddSuccessors(it.second, true);
    }

    addCFGEdges(F, finfo, lastNode);

    DBG(pta, "Added CFG structure to function '" << F->getName().str() << "'");

    finfo.has_structure = true;
}

PSNode *LLVMPointerGraphBuilder::connectArguments(const llvm::Function *F,
                                                  PSNodesBlock &argsBlk,
                                                  PointerSubgraph &subg) {
    PSNode *lastNode = nullptr;

    // make arguments the entry block of the subgraphs (if there
    // are any arguments)
    if (!argsBlk.empty()) {
        subg.root->addSuccessor(argsBlk.getFirstNode());

        // insert the variadic arg node into the graph if needed
        if (F->isVarArg()) {
            assert(subg.vararg);
            argsBlk.getLastNode()->addSuccessor(subg.vararg);
            lastNode = subg.vararg;
        } else {
            lastNode = argsBlk.getLastNode();
        }
    } else if (subg.vararg) {
        // this function has only ... argument
        assert(F->isVarArg());
        subg.root->addSuccessor(subg.vararg);
        lastNode = subg.vararg;
    } else {
        lastNode = subg.root;
    }

    return lastNode;
}

void LLVMPointerGraphBuilder::addCFGEdges(
        const llvm::Function *F, LLVMPointerGraphBuilder::FuncGraph &finfo,
        PSNode *lastNode) {
    // check whether we created the entry block. If not, we would
    // have a problem while adding successors, so fake that
    // the entry block is the root or the last argument
    const llvm::BasicBlock *entry = &F->front();
    auto it = finfo.llvmBlocks.find(entry);
    if (it != finfo.llvmBlocks.end()) {
        // if we have the entry block, just make it the successor
        // of the root or the last argument
        lastNode->addSuccessor(it->second.getFirstNode());
    } else {
        // Create a temporary PSNodesSeq with lastNode
        // and use it during adding successors for the
        // non-existing entry block
        PSNodesSeq seq(lastNode);
        PSNodesBlock blk(&seq);

        std::set<const llvm::BasicBlock *> found_blocks;
        finfo.blockAddSuccessors(found_blocks, blk, *entry);
    }

    for (auto &it : finfo.llvmBlocks) {
        auto &blk = it.second;
        assert(!blk.empty() && "Has empty block between built blocks");

        // add successors to this block (skipping the empty blocks).
        // To avoid infinite loops we use found_blocks container that will
        // serve as a marker in BFS/DFS - the program should not contain
        // so many blocks that this could have some big overhead. If proven
        // otherwise later, we'll change this.
        std::set<const llvm::BasicBlock *> found_blocks;
        finfo.blockAddSuccessors(found_blocks, blk, *it.first);
    }
}

} // namespace pta
} // namespace dg
