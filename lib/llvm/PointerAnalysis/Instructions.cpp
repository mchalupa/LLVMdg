#include "dg/llvm/PointerAnalysis/PointerGraph.h"
#include "llvm/llvm-utils.h"

namespace dg {
namespace pta {

LLVMPointerGraphBuilder::PSNodesSeq &
LLVMPointerGraphBuilder::createAlloc(const llvm::Instruction *Inst) {
    PSNodeAlloc *node = PSNodeAlloc::get(PS.create<PSNodeType::ALLOC>());

    const llvm::AllocaInst *AI = llvm::dyn_cast<llvm::AllocaInst>(Inst);
    if (AI)
        node->setSize(llvmutils::getAllocatedSize(AI, &M->getDataLayout()));

    return addNode(Inst, node);
}

LLVMPointerGraphBuilder::PSNodesSeq &
LLVMPointerGraphBuilder::createStore(const llvm::Instruction *Inst) {
    using namespace llvm;
    const Value *valOp = Inst->getOperand(0);

    PSNode *op1;
    if (isa<AtomicRMWInst>(valOp)) {
        // we store the old value of AtomicRMW
        auto it = nodes_map.find(valOp);
        if (it == nodes_map.end()) {
            op1 = UNKNOWN_MEMORY;
        } else {
            op1 = it->second.getFirst();
            assert(op1->getType() == PSNodeType::LOAD &&
                   "Invalid AtomicRMW nodes seq");
        }
    } else {
        op1 = getOperand(valOp);
    }

    PSNode *op2 = getOperand(Inst->getOperand(1));
    PSNode *node = PS.create<PSNodeType::STORE>(op1, op2);

    assert(node);
    return addNode(Inst, node);
}

PSNode *
LLVMPointerGraphBuilder::createInternalLoad(const llvm::Instruction *Inst) {
    const llvm::Value *op = Inst->getOperand(0);

    PSNode *op1 = getOperand(op);
    PSNode *node = PS.create<PSNodeType::LOAD>(op1);
    assert(node);

    return node;
}

LLVMPointerGraphBuilder::PSNodesSeq &
LLVMPointerGraphBuilder::createLoad(const llvm::Instruction *Inst) {
    return addNode(Inst, createInternalLoad(Inst));
}

LLVMPointerGraphBuilder::PSNodesSeq &
LLVMPointerGraphBuilder::createGEP(const llvm::Instruction *Inst) {
    using namespace llvm;

    const GetElementPtrInst *GEP = cast<GetElementPtrInst>(Inst);
    const Value *ptrOp = GEP->getPointerOperand();
    unsigned bitwidth =
            llvmutils::getPointerBitwidth(&M->getDataLayout(), ptrOp);
    APInt offset(bitwidth, 0);

    PSNode *node = nullptr;
    PSNode *op = getOperand(ptrOp);

    if (*_options.fieldSensitivity > 0 &&
        GEP->accumulateConstantOffset(M->getDataLayout(), offset)) {
        // is offset in given bitwidth?
        if (offset.isIntN(bitwidth)) {
            // is 0 < offset < field_sensitivity ?
            uint64_t off = offset.getLimitedValue(*_options.fieldSensitivity);
            if (off == 0 || off < *_options.fieldSensitivity)
                node = PS.create<PSNodeType::GEP>(op, offset.getZExtValue());
        } else
            errs() << "WARN: GEP offset greater than " << bitwidth << "-bit";
        // fall-through to Offset::UNKNOWN in this case
    }

    // we didn't create the node with concrete offset,
    // in which case we are supposed to create a node
    // with Offset::UNKNOWN
    if (!node)
        node = PS.create<PSNodeType::GEP>(op, Offset::UNKNOWN);

    assert(node);

    return addNode(Inst, node);
}

LLVMPointerGraphBuilder::PSNodesSeq &
LLVMPointerGraphBuilder::createSelect(const llvm::Instruction *Inst) {
    // with ptrtoint/inttoptr it may not be a pointer
    // assert(Inst->getType()->isPointerTy() && "BUG: This select is not a
    // pointer");

    // select <cond> <op1> <op2>
    PSNode *op1 = getOperand(Inst->getOperand(1));
    PSNode *op2 = getOperand(Inst->getOperand(2));

    // select works as a PHI in points-to analysis
    PSNode *node = PS.create<PSNodeType::PHI>(op1, op2);
    assert(node);

    return addNode(Inst, node);
}

Offset accumulateEVOffsets(const llvm::ExtractValueInst *EV,
                           const llvm::DataLayout &DL) {
    Offset off{0};
#if LLVM_VERSION_MAJOR >= 11
    llvm::Type *type = EV->getAggregateOperand()->getType();
#else
    llvm::CompositeType *type = llvm::dyn_cast<llvm::CompositeType>(
            EV->getAggregateOperand()->getType());
    assert(type && "Don't have composite type in extractvalue");
#endif

    for (unsigned idx : EV->getIndices()) {
        if (llvm::StructType *STy = llvm::dyn_cast<llvm::StructType>(type)) {
            assert(STy->indexValid(idx) && "Invalid index");
            const llvm::StructLayout *SL = DL.getStructLayout(STy);
            off += SL->getElementOffset(idx).getFixedValue();
        } else {
            // array or vector, so just move in the array
            if (auto *arrTy = llvm::dyn_cast<llvm::ArrayType>(type)) {
                assert(idx < arrTy->getNumElements() && "Invalid index");
                off += idx + DL.getTypeAllocSize(arrTy->getElementType());
            } else {
                auto *vecTy = llvm::cast<llvm::VectorType>(type);
#if LLVM_VERSION_MAJOR >= 12
                assert(idx < vecTy->getElementCount().getFixedValue() &&
                       "Invalid index");
#else
                assert(idx < vecTy->getNumElements() && "Invalid index");
#endif
                off += idx + DL.getTypeAllocSize(vecTy->getElementType());
            }
        }

#if LLVM_VERSION_MAJOR >= 11
        if (!llvm::GetElementPtrInst::getTypeAtIndex(type, idx))
#else
        if (!llvm::dyn_cast<llvm::CompositeType>(type->getTypeAtIndex(idx)))
#endif
            break; // we're done
    }

    return off;
}

LLVMPointerGraphBuilder::PSNodesSeq &
LLVMPointerGraphBuilder::createExtract(const llvm::Instruction *Inst) {
    using namespace llvm;

    const ExtractValueInst *EI = cast<ExtractValueInst>(Inst);

    // extract <agg> <idx> {<idx>, ...}
    PSNode *op1 = getOperand(EI->getAggregateOperand());
    PSNode *G = PS.create<PSNodeType::GEP>(
            op1, accumulateEVOffsets(EI, M->getDataLayout()));
    PSNode *L = PS.create<PSNodeType::LOAD>(G);

    // FIXME: add this later with all edges
    G->addSuccessor(L);

    PSNodesSeq ret({G, L});
    return addNode(Inst, ret);
}

LLVMPointerGraphBuilder::PSNodesSeq &
LLVMPointerGraphBuilder::createPHI(const llvm::Instruction *Inst) {
    PSNode *node = PS.create<PSNodeType::PHI>();
    assert(node);

    // NOTE: we didn't add operands to PHI node here, but after building
    // the whole function, because some blocks may not have been built
    // when we were creating the phi node

    return addNode(Inst, node);
}

LLVMPointerGraphBuilder::PSNodesSeq &
LLVMPointerGraphBuilder::createCast(const llvm::Instruction *Inst) {
    const llvm::Value *op = Inst->getOperand(0);
    PSNode *op1 = getOperand(op);
    PSNode *node = PS.create<PSNodeType::CAST>(op1);
    assert(node);
    return addNode(Inst, node);
}

// ptrToInt work just as a bitcast
LLVMPointerGraphBuilder::PSNodesSeq &
LLVMPointerGraphBuilder::createPtrToInt(const llvm::Instruction *Inst) {
    const llvm::Value *op = Inst->getOperand(0);

    PSNode *op1 = getOperand(op);
    // NOTE: we don't support arithmetic operations, so instead of
    // just casting the value do gep with unknown offset -
    // this way we cover any shift of the pointer due to arithmetic
    // operations
    // PSNode *node = PS.create(PSNodeType::CAST, op1);
    PSNode *node = PS.create<PSNodeType::GEP>(op1, 0);
    return addNode(Inst, node);
}

LLVMPointerGraphBuilder::PSNodesSeq &
LLVMPointerGraphBuilder::createIntToPtr(const llvm::Instruction *Inst) {
    const llvm::Value *op = Inst->getOperand(0);
    PSNode *op1;

    if (llvm::isa<llvm::Constant>(op)) {
        llvm::errs() << "PTA warning: IntToPtr with constant: " << *Inst
                     << "\n";
        // if this is inttoptr with constant, just make the pointer
        // unknown
        op1 = UNKNOWN_MEMORY;
    } else
        op1 = getOperand(op);

    PSNode *node = PS.create<PSNodeType::CAST>(op1);
    assert(node);

    return addNode(Inst, node);
}

LLVMPointerGraphBuilder::PSNodesSeq &
LLVMPointerGraphBuilder::createAdd(const llvm::Instruction *Inst) {
    using namespace llvm;

    PSNode *node;
    PSNode *op;
    const Value *val = nullptr;
    uint64_t off = Offset::UNKNOWN;

    if (isa<ConstantInt>(Inst->getOperand(0))) {
        op = getOperand(Inst->getOperand(1));
        val = Inst->getOperand(0);
    } else if (isa<ConstantInt>(Inst->getOperand(1))) {
        op = getOperand(Inst->getOperand(0));
        val = Inst->getOperand(1);
    } else {
        // the operands are both non-constant. Check if we
        // can get an operand as one of them and if not,
        // fall-back to unknown memory, because we
        // would need to track down both operads...
        op = tryGetOperand(Inst->getOperand(0));
        if (!op)
            op = tryGetOperand(Inst->getOperand(1));

        if (!op)
            return createUnknown(Inst);
    }

    assert(op && "Don't have operand for add");
    if (val)
        off = llvmutils::getConstantValue(val);

    node = PS.create<PSNodeType::GEP>(op, off);
    assert(node);

    return addNode(Inst, node);
}

LLVMPointerGraphBuilder::PSNodesSeq &
LLVMPointerGraphBuilder::createArithmetic(const llvm::Instruction *Inst) {
    using namespace llvm;

    PSNode *node;
    PSNode *op;

    // we don't know if the operand is the first or
    // the other operand
    if (isa<ConstantInt>(Inst->getOperand(0))) {
        op = getOperand(Inst->getOperand(1));
    } else if (isa<ConstantInt>(Inst->getOperand(0))) {
        op = getOperand(Inst->getOperand(0));
    } else {
        // the operands are both non-constant. Check if we
        // can get an operand as one of them and if not,
        // fall-back to unknown memory, because we
        // would need to track down both operads...
        op = tryGetOperand(Inst->getOperand(0));
        if (!op)
            op = tryGetOperand(Inst->getOperand(1));

        if (!op)
            return createUnknown(Inst);
    }

    // we don't know what the operation does,
    // so set unknown offset
    node = PS.create<PSNodeType::GEP>(op, Offset::UNKNOWN);
    assert(node);

    return addNode(Inst, node);
}

LLVMPointerGraphBuilder::PSNodesSeq &
LLVMPointerGraphBuilder::createReturn(const llvm::Instruction *Inst) {
    PSNode *op1 = nullptr;
    // is nullptr if this is 'ret void'
    llvm::Value *retVal = llvm::cast<llvm::ReturnInst>(Inst)->getReturnValue();

    // we create even void and non-pointer return nodes,
    // since these modify CFG (they won't bear any
    // points-to information though)
    // XXX is that needed?

    if (retVal) {
        // A struct is being returned. In this case,
        // return the address of the local variable
        // that holds the return value, so that
        // we can then do a load on this object
        if (retVal->getType()->isAggregateType()) {
            if (llvm::LoadInst *LI = llvm::dyn_cast<llvm::LoadInst>(retVal)) {
                op1 = getOperand(LI->getPointerOperand());
            }

            if (!op1) {
                llvm::errs()
                        << "WARN: Unsupported return of an aggregate type\n";
                llvm::errs() << *Inst << "\n";
                op1 = UNKNOWN_MEMORY;
            }
        } else if (retVal->getType()->isVectorTy()) {
            op1 = getOperand(retVal);
            if (auto *alloc = PSNodeAlloc::get(op1)) {
                assert(alloc->isTemporary());
                (void) alloc; // c++17 TODO: replace with [[maybe_unused]]
            } else {
                llvm::errs() << "WARN: Unsupported return of a vector\n";
                llvm::errs() << *Inst << "\n";
                op1 = UNKNOWN_MEMORY;
            }
        }

        if (llvm::isa<llvm::ConstantPointerNull>(retVal) ||
            llvmutils::isConstantZero(retVal))
            op1 = NULLPTR;
        else if (llvmutils::typeCanBePointer(&M->getDataLayout(),
                                             retVal->getType()) &&
                 (!isInvalid(retVal->stripPointerCasts(), invalidate_nodes) ||
                  llvm::isa<llvm::ConstantExpr>(retVal) ||
                  llvm::isa<llvm::UndefValue>(retVal)))
            op1 = getOperand(retVal);
    }

    assert((op1 || !retVal || !retVal->getType()->isPointerTy()) &&
           "Don't have an operand for ReturnInst with pointer");

    PSNode *node = op1 ? PS.create<PSNodeType::RETURN>(op1)
                       : PS.create<PSNodeType::RETURN>();
    assert(node);

    return addNode(Inst, node);
}

LLVMPointerGraphBuilder::PSNodesSeq &
LLVMPointerGraphBuilder::createInsertElement(const llvm::Instruction *Inst) {
    PSNodeAlloc *tempAlloc = nullptr;
    PSNode *lastNode = nullptr;
    PSNodesSeq seq;

    auto *Ty = llvm::cast<llvm::InsertElementInst>(Inst)->getType();
    auto elemSize = llvmutils::getAllocatedSize(Ty->getContainedType(0),
                                                &M->getDataLayout());
    auto *vec = Inst->getOperand(0);
    if (llvm::isa<llvm::UndefValue>(vec) || llvm::isa<llvm::Constant>(vec)) {
        tempAlloc = PSNodeAlloc::get(PS.create<PSNodeType::ALLOC>());
        tempAlloc->setIsTemporary();
        seq.append(tempAlloc);
        lastNode = tempAlloc;
        if (llvm::isa<llvm::Constant>(vec) &&
            !llvm::isa<llvm::UndefValue>(vec)) {
            // populate the allocation with elements of the constant
            unsigned idx = 0;
            for (auto &op : llvm::cast<llvm::ConstantVector>(vec)->operands()) {
                auto *ptr = getOperand(op);
                auto *GEP =
                        PS.create<PSNodeType::GEP>(tempAlloc, elemSize * idx);
                auto *S = PS.create<PSNodeType::STORE>(ptr, GEP);

                seq.append(GEP);
                seq.append(S);

                // TODO: do we need adding the successors here??
                lastNode->addSuccessor(GEP);
                GEP->addSuccessor(S);
                lastNode = S;
                ++idx;
            }
        }
    } else {
        auto *fromTempAlloc = PSNodeAlloc::get(getOperand(vec));
        assert(fromTempAlloc && "Is not an allocation node");
        assert(fromTempAlloc->isTemporary());

        tempAlloc = PSNodeAlloc::get(PS.create<PSNodeType::ALLOC>());
        tempAlloc->setIsTemporary();
        assert(tempAlloc);
        seq.append(tempAlloc);

        // copy old temporary allocation to the new temp allocation
        // (this is how insertelem works)
        auto *cpy = PS.create<PSNodeType::MEMCPY>(fromTempAlloc, tempAlloc,
                                                  Offset::UNKNOWN);
        seq.append(cpy);
        tempAlloc->addSuccessor(cpy);
        lastNode = cpy;
    }

    assert(tempAlloc && "Do not have the operand 0");
    seq.setRepresentant(tempAlloc);

    // write the pointers to the temporary allocation representing
    // the operand of insertelement
    auto *ptr = getOperand(Inst->getOperand(1));
    auto idx = llvmutils::getConstantValue(Inst->getOperand(2));
    assert(idx != ~((uint64_t) 0) && "Invalid index");

    // also, set the size of the temporary allocation
    tempAlloc->setSize(llvmutils::getAllocatedSize(Ty, &M->getDataLayout()));

    auto *GEP = PS.create<PSNodeType::GEP>(tempAlloc, elemSize * idx);
    auto *S = PS.create<PSNodeType::STORE>(ptr, GEP);

    seq.append(GEP);
    seq.append(S);

    lastNode->addSuccessor(GEP);
    GEP->addSuccessor(S);

    // this is a hack same as for call-inst.
    // We should really change the design here...
    tempAlloc->setPairedNode(S);

    return addNode(Inst, seq);
}

LLVMPointerGraphBuilder::PSNodesSeq &
LLVMPointerGraphBuilder::createExtractElement(const llvm::Instruction *Inst) {
    auto *op = getOperand(Inst->getOperand(0));
    assert(op && "Do not have the operand 0");

    auto idx = llvmutils::getConstantValue(Inst->getOperand(1));
    assert(idx != ~((uint64_t) 0) && "Invalid index");

    auto *Ty =
            llvm::cast<llvm::ExtractElementInst>(Inst)->getVectorOperandType();
    auto elemSize = llvmutils::getAllocatedSize(Ty->getContainedType(0),
                                                &M->getDataLayout());

    auto *GEP = PS.create<PSNodeType::GEP>(op, elemSize * idx);
    auto *L = PS.create<PSNodeType::LOAD>(GEP);

    GEP->addSuccessor(L);

    PSNodesSeq ret({GEP, L});
    return addNode(Inst, ret);
}

LLVMPointerGraphBuilder::PSNodesSeq &
LLVMPointerGraphBuilder::createAtomicRMW(const llvm::Instruction *Inst) {
    using namespace llvm;

    const auto *RMW = dyn_cast<AtomicRMWInst>(Inst);
    assert(RMW && "Wrong instruction");

    auto operation = RMW->getOperation();
    if (operation != AtomicRMWInst::Xchg && operation != AtomicRMWInst::Add &&
        operation != AtomicRMWInst::Sub) {
        return createUnknown(Inst);
    }

    auto *ptr = getOperand(RMW->getPointerOperand());
    Offset cval = Offset::UNKNOWN;

    auto *R = PS.create<PSNodeType::LOAD>(ptr);

    PSNode *M = nullptr;
    switch (operation) {
    case AtomicRMWInst::Xchg:
        M = getOperand(RMW->getValOperand());
        break;
    case AtomicRMWInst::Add:
        cval = Offset(llvmutils::getConstantValue(RMW->getValOperand()));
        M = PS.create<PSNodeType::GEP>(ptr, cval);
        R->addSuccessor(M);
        break;
    case AtomicRMWInst::Sub:
        break;
        cval = Offset(0) -
               Offset(llvmutils::getConstantValue(RMW->getValOperand()));
        M = PS.create<PSNodeType::GEP>(ptr, cval);
        R->addSuccessor(M);
        break;
    default:
        assert(false && "Invalid operation");
        abort();
    }
    assert(M);

    auto *W = PS.create<PSNodeType::STORE>(M, ptr);
    if (operation == AtomicRMWInst::Add || operation == AtomicRMWInst::Sub) {
        M->addSuccessor(W);
    }

    PSNodesSeq ret({R, W});
    return addNode(Inst, ret);
}

} // namespace pta
} // namespace dg
