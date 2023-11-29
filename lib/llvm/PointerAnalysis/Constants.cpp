#include "dg/llvm/PointerAnalysis/PointerGraph.h"
#include "llvm/llvm-utils.h"

namespace dg {
namespace pta {

Pointer
LLVMPointerGraphBuilder::handleConstantPtrToInt(const llvm::PtrToIntInst *P2I) {
    using namespace llvm;

    const Value *llvmOp = P2I->getOperand(0);
    // (possibly recursively) get the operand of this bit-cast
    PSNode *op = getOperand(llvmOp);
    assert(op->pointsTo.size() == 1 &&
           "Constant PtrToInt with not only one pointer");

    return *op->pointsTo.begin();
}

Pointer
LLVMPointerGraphBuilder::handleConstantIntToPtr(const llvm::IntToPtrInst *I2P) {
    using namespace llvm;

    const Value *llvmOp = I2P->getOperand(0);
    if (isa<ConstantInt>(llvmOp)) {
        llvm::errs() << "IntToPtr with constant: " << *I2P << "\n";
        return UnknownPointer;
    }

    // (possibly recursively) get the operand of this bit-cast
    PSNode *op = getOperand(llvmOp);
    assert(op->pointsTo.size() == 1 &&
           "Constant PtrToInt with not only one pointer");

    return *op->pointsTo.begin();
}

Pointer
LLVMPointerGraphBuilder::handleConstantAdd(const llvm::Instruction *Inst) {
    using namespace llvm;

    PSNode *op;
    const Value *val = nullptr;
    Offset off = Offset::UNKNOWN;

    // see createAdd() for details
    if (isa<ConstantInt>(Inst->getOperand(0))) {
        op = getOperand(Inst->getOperand(1));
        val = Inst->getOperand(0);
    } else if (isa<ConstantInt>(Inst->getOperand(1))) {
        op = getOperand(Inst->getOperand(0));
        val = Inst->getOperand(1);
    } else {
        op = tryGetOperand(Inst->getOperand(0));
        if (!op)
            op = tryGetOperand(Inst->getOperand(1));

        if (!op) {
            auto &unk = createUnknown(Inst);
            return Pointer{unk.getSingleNode(), Offset::UNKNOWN};
        }
    }

    assert(op && "Don't have operand for add");
    if (val)
        off = llvmutils::getConstantValue(val);

    assert(op->pointsTo.size() == 1 &&
           "Constant add with not only one pointer");

    Pointer ptr = *op->pointsTo.begin();
    if (off.isUnknown())
        return {ptr.target, Offset::UNKNOWN};
    return {ptr.target, ptr.offset + off};
}

Pointer LLVMPointerGraphBuilder::handleConstantArithmetic(
        const llvm::Instruction *Inst) {
    using namespace llvm;

    PSNode *op;

    if (isa<ConstantInt>(Inst->getOperand(0))) {
        op = getOperand(Inst->getOperand(1));
    } else if (isa<ConstantInt>(Inst->getOperand(1))) {
        op = getOperand(Inst->getOperand(0));
    } else {
        op = tryGetOperand(Inst->getOperand(0));
        if (!op)
            op = tryGetOperand(Inst->getOperand(1));

        if (!op)
            return Pointer{createUnknown(Inst).getSingleNode(),
                           Offset::UNKNOWN};
    }

    assert(op && "Don't have operand for add");
    assert(op->pointsTo.size() == 1 &&
           "Constant add with not only one pointer");

    Pointer ptr = *op->pointsTo.begin();
    return {ptr.target, Offset::UNKNOWN};
}

Pointer
LLVMPointerGraphBuilder::handleConstantBitCast(const llvm::CastInst *BC) {
    using namespace llvm;

    if (!BC->getSrcTy()->canLosslesslyBitCastTo(BC->getDestTy())) {
        // If this is a cast to a bigger type (if that can ever happen?),
        // then preserve the pointer. Otherwise, the pointer is cropped,
        // and there's nothing we can do...
        if (!llvmutils::typeCanBePointer(&M->getDataLayout(), BC->getType()))
            return UnknownPointer;
        // fall-through
    }

    const Value *llvmOp = BC->stripPointerCasts();
    // (possibly recursively) get the operand of this bit-cast
    PSNode *op = getOperand(llvmOp);
    assert(op->pointsTo.size() == 1 &&
           "Constant BitCast with not only one pointer");

    return *op->pointsTo.begin();
}

Pointer
LLVMPointerGraphBuilder::handleConstantGep(const llvm::GetElementPtrInst *GEP) {
    using namespace llvm;

    const Value *op = GEP->getPointerOperand();
    Pointer pointer(UNKNOWN_MEMORY, Offset::UNKNOWN);

    // get operand PSNode (this may result in recursive call,
    // if this gep is recursively defined)
    PSNode *opNode = getOperand(op);
    assert(opNode->pointsTo.size() == 1 &&
           "Constant node has more that 1 pointer");
    pointer = *(opNode->pointsTo.begin());

    unsigned bitwidth = llvmutils::getPointerBitwidth(&M->getDataLayout(), op);
    APInt offset(bitwidth, 0);

    // get offset of this GEP
    if (GEP->accumulateConstantOffset(M->getDataLayout(), offset)) {
        if (offset.isIntN(bitwidth) && !pointer.offset.isUnknown())
            pointer.offset = offset.getZExtValue();
        else
            errs() << "WARN: Offset greater than " << bitwidth << "-bit" << *GEP
                   << "\n";
    }

    return pointer;
}

Pointer
LLVMPointerGraphBuilder::getConstantExprPointer(const llvm::ConstantExpr *CE) {
    using namespace llvm;

    Pointer pointer(UNKNOWN_MEMORY, Offset::UNKNOWN);
    Instruction *Inst = const_cast<ConstantExpr *>(CE)->getAsInstruction();

    switch (Inst->getOpcode()) {
    case Instruction::GetElementPtr:
        pointer = handleConstantGep(cast<GetElementPtrInst>(Inst));
        break;
        // case Instruction::ExtractValue:
        // case Instruction::Select:
        break;
    case Instruction::BitCast:
    case Instruction::SExt:
    case Instruction::ZExt:
        pointer = handleConstantBitCast(cast<CastInst>(Inst));
        break;
    case Instruction::PtrToInt:
        pointer = handleConstantPtrToInt(cast<PtrToIntInst>(Inst));
        break;
    case Instruction::IntToPtr:
        pointer = handleConstantIntToPtr(cast<IntToPtrInst>(Inst));
        break;
    case Instruction::Add:
        pointer = handleConstantAdd(Inst);
        break;
    case Instruction::And:
    case Instruction::Or:
    case Instruction::Trunc:
    case Instruction::Shl:
    case Instruction::LShr:
    case Instruction::AShr:
        pointer = UnknownPointer;
        break;
    case Instruction::Sub:
    case Instruction::Mul:
    case Instruction::SDiv:
        pointer = handleConstantArithmetic(Inst);
        break;
    default:
        errs() << "ERR: Unsupported ConstantExpr " << *CE << "\n";
        abort();
    }

#if LLVM_VERSION_MAJOR < 5
    delete Inst;
#else
    Inst->deleteValue();
#endif
    return pointer;
}

LLVMPointerGraphBuilder::PSNodesSeq &
LLVMPointerGraphBuilder::createConstantExpr(const llvm::ConstantExpr *CE) {
    Pointer ptr = getConstantExprPointer(CE);
    PSNode *node = PS.create<PSNodeType::CONSTANT>(ptr.target, ptr.offset);

    return addNode(CE, node);
}

LLVMPointerGraphBuilder::PSNodesSeq &
LLVMPointerGraphBuilder::createUnknown(const llvm::Value *val) {
    // nothing better we can do, these operations
    // completely change the value of pointer...

    // FIXME: or there's enough unknown offset? Check it out!
    PSNode *node =
            PS.create<PSNodeType::CONSTANT>(UNKNOWN_MEMORY, Offset::UNKNOWN);
    assert(node);

    return addNode(val, node);
}

} // namespace pta
} // namespace dg
