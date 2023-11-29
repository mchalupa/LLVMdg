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

namespace dg {
namespace pta {

void LLVMPointerGraphBuilder::handleGlobalVariableInitializer(
        const llvm::Constant *C, PSNodeAlloc *node, uint64_t offset) {
    using namespace llvm;

    // if the global is zero initialized, just set the zeroInitialized flag
    if (C->isNullValue()) {
        node->setZeroInitialized();
    } else if (C->getType()->isStructTy()) {
        uint64_t off = 0;
        auto *STy = cast<StructType>(C->getType());
        const StructLayout *SL = M->getDataLayout().getStructLayout(STy);
        int i = 0;
        for (auto I = C->op_begin(), E = C->op_end(); I != E; ++I, ++i) {
            const Constant *op = cast<Constant>(*I);
            // recursively dive into the aggregate type
            off = SL->getElementOffset(i);
            handleGlobalVariableInitializer(op, node, offset + off);
        }
    } else if (C->getType()->isArrayTy()) {
        uint64_t off = 0;
        for (auto I = C->op_begin(), E = C->op_end(); I != E; ++I) {
            const Constant *op = cast<Constant>(*I);
            Type *Ty = op->getType();
            // recursively dive into the aggregate type
            handleGlobalVariableInitializer(op, node, offset + off);
            off += M->getDataLayout().getTypeAllocSize(Ty);
        }
    } else if (C->getType()->isPointerTy()) {
        PSNode *op = getOperand(C);
        PSNode *target = PS.createGlobal<PSNodeType::CONSTANT>(node, offset);
        PS.createGlobal<PSNodeType::STORE>(op, target);
    } else if (isa<ConstantExpr>(C) || isa<Function>(C) ||
               C->getType()->isPointerTy()) {
        if (C->getType()->isPointerTy()) {
            PSNode *value = getOperand(C);
            assert(value->pointsTo.size() == 1 &&
                   "BUG: We should have constant");
            PS.createGlobal<PSNodeType::STORE>(value, node);
        }
    } else if (isa<UndefValue>(C)) {
        // undef value means unknown memory
        PSNode *target = PS.createGlobal<PSNodeType::CONSTANT>(node, offset);
        PS.createGlobal<PSNodeType::STORE>(UNKNOWN_MEMORY, target);
    } else if (!isa<ConstantInt>(C) && !isa<ConstantFP>(C)) {
        llvm::errs() << *C << "\n";
        llvm::errs() << "ERROR: ^^^ global variable initializer not handled\n";
        abort();
    }
}

static uint64_t getAllocatedSize(const llvm::GlobalVariable *GV,
                                 const llvm::DataLayout *DL) {
    if (!GV->hasInitializer())
        return 0;
    llvm::Type *Ty = GV->getInitializer()->getType();
    if (!Ty->isSized())
        return 0;

    return DL->getTypeAllocSize(Ty);
}

void LLVMPointerGraphBuilder::buildGlobals() {
    // create PointerGraph nodes
    for (auto I = M->global_begin(), E = M->global_end(); I != E; ++I) {
        // every global node is like memory allocation
        PSNodeAlloc *nd =
                PSNodeAlloc::get(PS.createGlobal<PSNodeType::ALLOC>());
        nd->setIsGlobal();
        addNode(&*I, nd);
    }

    // only now handle the initializers - we need to have then
    // built, because they can point to each other
    for (auto I = M->global_begin(), E = M->global_end(); I != E; ++I) {
        PSNodeAlloc *node = PSNodeAlloc::get(getNodes(&*I)->getSingleNode());
        assert(node && "BUG: Do not have global variable"
                       " or it is not an allocation");

        // handle globals initialization
        if (const auto *const GV = llvm::dyn_cast<llvm::GlobalVariable>(&*I)) {
            node->setSize(getAllocatedSize(GV, &M->getDataLayout()));

            if (GV->hasInitializer() && !GV->isExternallyInitialized()) {
                const llvm::Constant *C = GV->getInitializer();
                handleGlobalVariableInitializer(C, node);
            }
        } else {
            // without initializer we can not do anything else than
            // assume that it can point everywhere
            PS.createGlobal<PSNodeType::STORE>(UNKNOWN_MEMORY, node);
        }
    }
}

} // namespace pta
} // namespace dg
