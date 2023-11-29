#include "dg/llvm/ValueRelations/RelationsAnalyzer.h"

#include <algorithm>

namespace dg {
namespace vr {

using V = ValueRelations::V;

// ********************** points to invalidation ********************** //
bool RelationsAnalyzer::isIgnorableIntrinsic(llvm::Intrinsic::ID id) {
    switch (id) {
    case llvm::Intrinsic::lifetime_start:
    case llvm::Intrinsic::lifetime_end:
    case llvm::Intrinsic::stacksave:
    case llvm::Intrinsic::stackrestore:
    case llvm::Intrinsic::dbg_declare:
    case llvm::Intrinsic::dbg_value:
        return true;
    default:
        return false;
    }
}

bool RelationsAnalyzer::isSafe(I inst) const {
    if (!inst->mayWriteToMemory() && !inst->mayHaveSideEffects())
        return true;

    if (const auto *intrinsic = llvm::dyn_cast<llvm::IntrinsicInst>(inst)) {
        if (isIgnorableIntrinsic(intrinsic->getIntrinsicID())) {
            return true;
        }
    }

    if (const auto *call = llvm::dyn_cast<llvm::CallInst>(inst)) {
        const auto *function = call->getCalledFunction();
        if (function && safeFunctions.find(function->getName().str()) !=
                                safeFunctions.end())
            return true;
    }
    return false;
}

bool RelationsAnalyzer::isDangerous(I inst) {
    const auto *store = llvm::dyn_cast<llvm::StoreInst>(inst);
    if (!store) // most probably CallInst
        // unable to presume anything about such instruction
        return true;

    // if store writes to a fix location, it cannot be easily said which
    // values it affects
    if (llvm::isa<llvm::Constant>(store->getPointerOperand()))
        return true;

    return false;
}

bool RelationsAnalyzer::mayHaveAlias(const ValueRelations &graph, V val) const {
    for (const auto *eqval : graph.getEqual(val)) {
        if (!hasKnownOrigin(graph, eqval) || mayHaveAlias(eqval))
            return true;
    }
    return false;
}

bool RelationsAnalyzer::mayHaveAlias(V val) const {
    // if value is not pointer, we don't care whether there can be other name
    // for same value
    if (!val->getType()->isPointerTy())
        return false;

    if (llvm::isa<llvm::GetElementPtrInst>(val))
        return true;

    for (const llvm::User *user : val->users()) {
        // if value is stored, it can be accessed
        if (llvm::isa<llvm::StoreInst>(user)) {
            if (user->getOperand(0) == val)
                return true;

        } else if (llvm::isa<llvm::CastInst>(user)) {
            if (mayHaveAlias(user))
                return true;

        } else if (llvm::isa<llvm::GetElementPtrInst>(user)) {
            return true; // TODO possible to collect here

        } else if (const auto *intrinsic =
                           llvm::dyn_cast<llvm::IntrinsicInst>(user)) {
            if (!isIgnorableIntrinsic(intrinsic->getIntrinsicID()) &&
                intrinsic->mayWriteToMemory())
                return true;

        } else if (const auto *inst = llvm::dyn_cast<llvm::Instruction>(user)) {
            if (inst->mayWriteToMemory())
                return true;
        }
    }
    return false;
}

bool RelationsAnalyzer::hasKnownOrigin(const ValueRelations &graph, V from) {
    for (const auto *val : graph.getEqual(from)) {
        if (hasKnownOrigin(val))
            return true;
    }
    return false;
}

bool RelationsAnalyzer::hasKnownOrigin(V from) {
    return llvm::isa<llvm::AllocaInst>(from);
}

V getGEPBase(V val) {
    if (const auto *gep = llvm::dyn_cast<llvm::GetElementPtrInst>(val))
        return gep->getPointerOperand();
    return nullptr;
}

bool sameBase(const ValueRelations &graph, V val1, V val2) {
    V val2orig = val2;
    while (val1) {
        val2 = val2orig;
        while (val2) {
            if (graph.are(val1, Relations::EQ,
                          val2)) // TODO compare whether indices may equal
                return true;
            val2 = getGEPBase(val2);
        }
        val1 = getGEPBase(val1);
    }
    return false;
}

bool RelationsAnalyzer::mayOverwrite(I inst, V address) const {
    assert(inst);
    assert(address);

    const ValueRelations &graph = codeGraph.getVRLocation(inst).relations;

    if (isSafe(inst))
        return false;

    if (isDangerous(inst))
        return true;

    const auto *store = llvm::cast<llvm::StoreInst>(inst);
    V memoryPtr = store->getPointerOperand();

    return sameBase(graph, memoryPtr, address) ||
           (!hasKnownOrigin(graph, memoryPtr) &&
            mayHaveAlias(graph, address)) ||
           (mayHaveAlias(graph, memoryPtr) && !hasKnownOrigin(graph, address));
}

const llvm::Argument *getArgument(const ValueRelations &graph,
                                  ValueRelations::Handle h) {
    const llvm::Argument *result = nullptr;
    for (auto handleRel : graph.getRelated(h, Relations().sle().sge())) {
        const llvm::Argument *arg =
                graph.getInstance<llvm::Argument>(handleRel.first);
        if (arg) {
            assert(!result);
            result = arg;
        }
    }
    return result;
}

// ************************ operation helpers ************************* //
bool RelationsAnalyzer::operandsEqual(
        ValueRelations &graph, I fst, I snd,
        bool sameOrder) { // false means checking in reverse order
    unsigned total = fst->getNumOperands();
    if (total != snd->getNumOperands())
        return false;

    for (unsigned i = 0; i < total; ++i) {
        unsigned otherI = sameOrder ? i : total - i - 1;

        if (!graph.isEqual(fst->getOperand(i), snd->getOperand(otherI)))
            return false;
    }
    return true;
}

void RelationsAnalyzer::solveByOperands(ValueRelations &graph,
                                        const llvm::BinaryOperator *operation,
                                        bool sameOrder) {
    for (const auto *same :
         structure.getInstructionSetFor(operation->getOpcode())) {
        assert(llvm::isa<const llvm::BinaryOperator>(same));
        const auto *sameOperation =
                llvm::cast<const llvm::BinaryOperator>(same);

        if (operation != sameOperation &&
            operandsEqual(graph, operation, sameOperation, sameOrder))
            graph.setEqual(operation, sameOperation);
    }
}

void RelationsAnalyzer::solveEquality(ValueRelations &graph,
                                      const llvm::BinaryOperator *operation) {
    solveByOperands(graph, operation, true);
}

void RelationsAnalyzer::solveCommutativity(
        ValueRelations &graph, const llvm::BinaryOperator *operation) {
    solveByOperands(graph, operation, false);
}

// ******************** gen from instruction ************************** //
void RelationsAnalyzer::storeGen(ValueRelations &graph,
                                 const llvm::StoreInst *store) {
    graph.setLoad(store->getPointerOperand()->stripPointerCasts(),
                  store->getValueOperand());
}

void RelationsAnalyzer::loadGen(ValueRelations &graph,
                                const llvm::LoadInst *load) {
    graph.setLoad(load->getPointerOperand()->stripPointerCasts(), load);
}

int toChange(const llvm::GetElementPtrInst *gep) {
    if (gep->getNumIndices() != 1)
        return 0;
    if (const auto *i = llvm::dyn_cast<llvm::ConstantInt>(gep->getOperand(1))) {
        if (i->isOne())
            return 1;
        if (i->isMinusOne())
            return -1;
    }
    return 0;
}

void RelationsAnalyzer::gepGen(ValueRelations &graph,
                               const llvm::GetElementPtrInst *gep) {
    if (gep->hasAllZeroIndices())
        graph.setEqual(gep, gep->getPointerOperand());

    int thisChange = toChange(gep);
    if (const auto *origGep = graph.getInstance<llvm::GetElementPtrInst>(
                gep->getPointerOperand())) {
        int origChange = toChange(origGep);
        if (thisChange && origChange && thisChange + origChange == 0)
            graph.set(gep, Relations::EQ, origGep->getPointerOperand());
    }

    if (thisChange)
        graph.set(gep->getPointerOperand(),
                  thisChange == 1 ? Relations::SLT : Relations::SGT, gep);

    for (auto it = graph.begin_buckets(Relations().pt());
         it != graph.end_buckets(); ++it) {
        for (V from : graph.getEqual(it->from())) {
            if (const auto *otherGep =
                        llvm::dyn_cast<llvm::GetElementPtrInst>(from)) {
                if (operandsEqual(graph, gep, otherGep, true)) {
                    graph.setEqual(gep, otherGep);
                    return;
                }
            }
        }
    }
    // TODO something more?
    // indices method gives iterator over indices
}

void RelationsAnalyzer::extGen(ValueRelations &graph,
                               const llvm::CastInst *ext) {
    graph.setEqual(ext, ext->getOperand(0));
}

void solveNonConstants(ValueRelations &graph,
                       llvm::Instruction::BinaryOps opcode,
                       const llvm::BinaryOperator *op) {
    if (opcode != llvm::Instruction::Sub)
        return;

    const llvm::Constant *zero = llvm::ConstantInt::getSigned(op->getType(), 0);
    V fst = op->getOperand(0);
    V snd = op->getOperand(1);

    if (graph.isLesser(zero, snd) && graph.isLesserEqual(snd, fst))
        graph.setLesser(op, fst);
}

std::pair<llvm::Value *, llvm::ConstantInt *>
getParams(const llvm::BinaryOperator *op) {
    if (llvm::isa<llvm::ConstantInt>(op->getOperand(0))) {
        assert(!llvm::isa<llvm::ConstantInt>(op->getOperand(1)));
        if (op->getOpcode() == llvm::Instruction::Sub)
            return {nullptr, nullptr};
        return {op->getOperand(1),
                llvm::cast<llvm::ConstantInt>(op->getOperand(0))};
    }
    return {op->getOperand(0),
            llvm::cast<llvm::ConstantInt>(op->getOperand(1))};
}

RelationsAnalyzer::Shift
RelationsAnalyzer::getShift(const llvm::BinaryOperator *op,
                            const VectorSet<V> &froms) {
    if (llvm::isa<llvm::ConstantInt>(op->getOperand(0)) ==
        llvm::isa<llvm::ConstantInt>(op->getOperand(1)))
        return Shift::UNKNOWN;
    V param = nullptr;
    llvm::ConstantInt *c = nullptr;
    std::tie(param, c) = getParams(op);

    assert(param && c);
    auto load = llvm::dyn_cast<llvm::LoadInst>(param);
    if (!load || !froms.contains(load->getPointerOperand()))
        return Shift::UNKNOWN;

    auto opcode = op->getOpcode();
    if ((opcode == llvm::Instruction::Add && c->isOne()) ||
        (opcode == llvm::Instruction::Sub && c->isMinusOne())) {
        return Shift::INC;
    }
    if ((opcode == llvm::Instruction::Add && c->isMinusOne()) ||
        (opcode == llvm::Instruction::Sub && c->isOne())) {
        return Shift::DEC;
    }
    return Shift::UNKNOWN;
}

RelationsAnalyzer::Shift
RelationsAnalyzer::getShift(const llvm::GetElementPtrInst *op,
                            const VectorSet<V> &froms) {
    V ptr = op->getPointerOperand();
    auto load = llvm::dyn_cast<llvm::LoadInst>(ptr);
    if (!load || !froms.contains(load->getPointerOperand()))
        return Shift::UNKNOWN;
    if (const auto *i = llvm::dyn_cast<llvm::ConstantInt>(op->getOperand(1))) {
        if (i->isOne())
            return Shift::INC;
        if (i->isMinusOne())
            return Shift::DEC;
    }
    return Shift::UNKNOWN;
}

RelationsAnalyzer::Shift
RelationsAnalyzer::getShift(const llvm::Value *val, const VectorSet<V> &froms) {
    if (auto op = llvm::dyn_cast<llvm::BinaryOperator>(val))
        return getShift(op, froms);
    if (auto op = llvm::dyn_cast<llvm::GetElementPtrInst>(val))
        return getShift(op, froms);
    return Shift::UNKNOWN;
}

RelationsAnalyzer::Shift RelationsAnalyzer::getShift(
        const std::vector<const VRLocation *> &changeLocations,
        const VectorSet<V> &froms) const {
    Shift shift = Shift::EQ;
    // first location is the tree predecessor
    for (auto it = std::next(changeLocations.begin());
         it != changeLocations.end(); ++it) {
        const VRLocation *loc = *it;
        assert(loc->predsSize() == 1);

        V inst = static_cast<VRInstruction *>(loc->getPredEdge(0)->op.get())
                         ->getInstruction();
        assert(inst);
        assert(llvm::isa<llvm::StoreInst>(inst));
        const llvm::StoreInst *store = llvm::cast<llvm::StoreInst>(inst);
        if (!froms.contains(store->getPointerOperand()))
            return Shift::UNKNOWN;

        const auto *what = store->getValueOperand();

        Shift current = getShift(what, froms);

        if (shift == Shift::UNKNOWN)
            return shift;
        if (shift == Shift::EQ)
            shift = current;
        else if (shift != current)
            return Shift::UNKNOWN;
    }
    return shift;
}

bool RelationsAnalyzer::canShift(const ValueRelations &graph, V param,
                                 Relations::Type shift) {
    const auto *paramType = param->getType();
    assert(Relations::isStrict(shift) && Relations::isSigned(shift));
    if (!graph.hasAnyRelation(param) || !param->getType()->isIntegerTy())
        return false;

    // if there is a value lesser/greater with same or smaller range, then param
    // is also inc/decrementable
    for (auto pair : graph.getRelated(
                 param,
                 Relations().set(shift).set(Relations::getNonStrict(shift)))) {
        for (const auto &val : graph.getEqual(pair.first)) {
            const auto *valType = val->getType();
            if (valType->isIntegerTy() &&
                valType->getIntegerBitWidth() <=
                        paramType->getIntegerBitWidth()) {
                if (pair.second.has(shift))
                    return true;
                assert(pair.second.has(Relations::getNonStrict(shift)));
                if (const auto *c = llvm::dyn_cast<llvm::ConstantInt>(val)) {
                    if (!(shift == Relations::SGT && c->isMinValue(true)) &&
                        !(shift == Relations::SLT && c->isMaxValue(true)))
                        return true;
                }
            }
        }
    }

    // if the shifted value is a parameter, it depends on the passed value;
    // check when validating
    if (const auto *paramInst = llvm::dyn_cast<llvm::Instruction>(param)) {
        const llvm::Function *thisFun = paramInst->getFunction();

        for (const auto *val : graph.getEqual(paramInst)) {
            if (const auto *arg = llvm::dyn_cast<llvm::Argument>(val)) {
                if (arg->getType()->isIntegerTy()) {
                    const auto *zero =
                            llvm::ConstantInt::get(arg->getType(), 0);
                    if (graph.are(arg, Relations::NE, zero))
                        structure.addPrecondition(
                                thisFun, arg, Relations::getNonStrict(shift),
                                zero);
                    else
                        structure.addPrecondition(thisFun, arg, shift, zero);
                    return true;
                }
            }
        }
    }
    return false;
}

void RelationsAnalyzer::solveDifferent(ValueRelations &graph,
                                       const llvm::BinaryOperator *op) {
    auto opcode = op->getOpcode();

    V param = nullptr;
    llvm::ConstantInt *c = nullptr;
    std::tie(param, c) = getParams(op);

    if (!param)
        return;

    assert(param && c);

    Relations::Type shift;
    if ((opcode == llvm::Instruction::Add && c->isOne()) ||
        (opcode == llvm::Instruction::Sub && c->isMinusOne())) {
        shift = Relations::SLT;
    } else if ((opcode == llvm::Instruction::Add && c->isMinusOne()) ||
               (opcode == llvm::Instruction::Sub && c->isOne())) {
        shift = Relations::SGT;
    } else
        return;

    if (canShift(graph, param, shift)) {
        graph.set(param, shift, op);

        std::vector<V> sample =
                graph.getDirectlyRelated(param, Relations().set(shift));

        for (V val : sample) {
            assert(graph.are(param, shift, val));
            graph.set(op, Relations::getNonStrict(shift), val);
        }

        auto boundC = graph.getBound(param, Relations::getNonStrict(shift));
        if (boundC.first && boundC.second.has(Relations::getNonStrict(shift)) &&
            !graph.are(op, Relations::getNonStrict(shift), boundC.first)) {
            int64_t intC = boundC.first->getSExtValue();
            intC += shift == Relations::SLT ? 1 : -1;
            const auto *newBound =
                    llvm::ConstantInt::get(boundC.first->getType(), intC, true);
            graph.set(op, Relations::getNonStrict(shift), newBound);
        }
    }
}

void RelationsAnalyzer::opGen(ValueRelations &graph,
                              const llvm::BinaryOperator *op) {
    const auto *c1 = llvm::dyn_cast<llvm::ConstantInt>(op->getOperand(0));
    const auto *c2 = llvm::dyn_cast<llvm::ConstantInt>(op->getOperand(1));
    auto opcode = op->getOpcode();

    solveEquality(graph, op);
    if (opcode == llvm::Instruction::Add || opcode == llvm::Instruction::Mul)
        solveCommutativity(graph, op);

    if (opcode == llvm::Instruction::Mul)
        return;

    if (c1 && c2)
        return;

    if (!c1 && !c2)
        return solveNonConstants(graph, opcode, op);

    solveDifferent(graph, op);
}

void RelationsAnalyzer::remGen(ValueRelations &graph,
                               const llvm::BinaryOperator *rem) {
    assert(rem);
    const llvm::Constant *zero =
            llvm::ConstantInt::getSigned(rem->getType(), 0);

    if (!graph.isLesserEqual(zero, rem->getOperand(0)))
        return;

    graph.setLesserEqual(zero, rem);
    graph.setLesser(rem, rem->getOperand(1));
}

void RelationsAnalyzer::castGen(ValueRelations &graph,
                                const llvm::CastInst *cast) {
    if (cast->getSrcTy()->canLosslesslyBitCastTo(cast->getDestTy()) ||
        cast->isNoopCast(module.getDataLayout()))
        graph.setEqual(cast, cast->getOperand(0));
}

// ******************** process assumption ************************** //
RelationsAnalyzer::Relation
RelationsAnalyzer::ICMPToRel(const llvm::ICmpInst *icmp, bool assumption) {
    llvm::ICmpInst::Predicate pred = assumption ? icmp->getSignedPredicate()
                                                : icmp->getInversePredicate();

    switch (pred) {
    case llvm::ICmpInst::Predicate::ICMP_EQ:
        return Relation::EQ;
    case llvm::ICmpInst::Predicate::ICMP_NE:
        return Relation::NE;
    case llvm::ICmpInst::Predicate::ICMP_ULE:
        return Relation::ULE;
    case llvm::ICmpInst::Predicate::ICMP_SLE:
        return Relation::SLE;
    case llvm::ICmpInst::Predicate::ICMP_ULT:
        return Relation::ULT;
    case llvm::ICmpInst::Predicate::ICMP_SLT:
        return Relation::SLT;
    case llvm::ICmpInst::Predicate::ICMP_UGE:
        return Relation::UGE;
    case llvm::ICmpInst::Predicate::ICMP_SGE:
        return Relation::SGE;
    case llvm::ICmpInst::Predicate::ICMP_UGT:
        return Relation::UGT;
    case llvm::ICmpInst::Predicate::ICMP_SGT:
        return Relation::SGT;
    default:
#ifndef NDEBUG
        llvm::errs() << "Unhandled predicate in" << *icmp << "\n";
#endif
        abort();
    }
}

size_t limitingBorder(const ValueRelations &relations, const llvm::Value *val) {
    for (const auto &handleRel : relations.getRelated(val, Relations().sle())) {
        auto mId = relations.getBorderId(handleRel.first);
        if (mId != std::string::npos)
            return mId;
    }
    return std::string::npos;
}

bool RelationsAnalyzer::findEqualBorderBucket(const ValueRelations &relations,
                                              const llvm::Value *mBorderV,
                                              const llvm::Value *comparedV) {
    if (!llvm::isa<llvm::Instruction>(mBorderV) ||
        !llvm::isa<llvm::Instruction>(comparedV))
        return false;
    if (!relations.contains(mBorderV) || !relations.contains(comparedV))
        return false;

    const auto &borderFroms = getFroms(relations, mBorderV);
    const auto &comparedFroms = getFroms(relations, comparedV);

    if (borderFroms.size() != 2 || comparedFroms.size() != 2)
        return false;

    auto mBorderId = limitingBorder(relations, borderFroms[0]);
    if (mBorderId == std::string::npos)
        return false;

    // if (limitingBorder(relations, comparedFroms[0]) != std::string::npos)
    //     return true;

    const llvm::Argument *arg =
            getArgument(relations, *relations.getHandle(comparedFroms[0]));
    if (!arg)
        return false;

    const auto *comparedFrom = llvm::cast<llvm::Instruction>(comparedFroms[0]);
    const auto *func = comparedFrom->getFunction();
    assert(structure.hasBorderValues(func));
    BorderValue bv = structure.getBorderValueFor(func, mBorderId);
    for (const auto &borderVal : structure.getBorderValuesFor(func)) {
        if (borderVal.from == arg && borderVal.stored == bv.stored) {
            assert(codeGraph.getVRLocation(comparedFrom)
                           .getSuccLocation(0)
                           ->join);
            VRLocation &join = const_cast<VRLocation &>(
                    *codeGraph.getVRLocation(comparedFrom)
                             .getSuccLocation(0)
                             ->join);
            assert(join.relations.has(comparedFroms[1], Relations::PT));
            const auto &placeholder =
                    join.relations.getPointedTo(comparedFroms[1]);

            auto thisBorderPlaceholder =
                    join.relations.getBorderH(borderVal.id);
            assert(thisBorderPlaceholder);
            join.relations.set(placeholder, Relations::SLE,
                               *thisBorderPlaceholder);
            return true;
        }
    }

    auto id = structure.addBorderValue(func, arg, bv.stored);
    ValueRelations &entryRels = codeGraph.getEntryLocation(*func).relations;
    Handle entryBorderPlaceholder = entryRels.newBorderBucket(id);
    entryRels.set(entryBorderPlaceholder, Relations::PT, bv.stored);
    entryRels.set(entryBorderPlaceholder, Relations::SGE, arg);
    return true;
}

bool RelationsAnalyzer::processICMP(const ValueRelations &oldGraph,
                                    ValueRelations &newGraph,
                                    VRAssumeBool *assume) {
    const llvm::ICmpInst *icmp = llvm::cast<llvm::ICmpInst>(assume->getValue());
    bool assumption = assume->getAssumption();

    V op1 = icmp->getOperand(0);
    V op2 = icmp->getOperand(1);

    Relation rel = ICMPToRel(icmp, assumption);

    if (oldGraph.hasConflictingRelation(op1, op2, rel))
        return false;

    newGraph.set(op1, rel, op2);

    if (rel == Relations::EQ) {
        if (!findEqualBorderBucket(oldGraph, op1, op2))
            findEqualBorderBucket(oldGraph, op2, op1);
    }
    return true;
}

std::pair<const llvm::LoadInst *, const llvm::Value *>
getParams(const ValueRelations &graph, const llvm::ICmpInst *icmp) {
    const llvm::Value *op1 = icmp->getOperand(0);
    const llvm::Value *op2 = icmp->getOperand(1);
    if (const auto *load = graph.getInstance<llvm::LoadInst>(op1))
        return {load, op2};
    if (const auto *load = graph.getInstance<llvm::LoadInst>(op2))
        return {load, op1};
    return {nullptr, nullptr};
}

void RelationsAnalyzer::inferFromNEPointers(ValueRelations &newGraph,
                                            VRAssumeBool *assume) const {
    const llvm::ICmpInst *icmp =
            llvm::dyn_cast<llvm::ICmpInst>(assume->getValue());
    if (!icmp)
        return;
    bool assumption = assume->getAssumption();
    Relation rel = ICMPToRel(icmp, assumption);

    const llvm::LoadInst *load;
    const llvm::Value *compared;
    std::tie(load, compared) = getParams(newGraph, icmp);
    if (!load || (rel != Relations::EQ && rel != Relations::NE))
        return;

    for (auto related : newGraph.getRelated(load->getPointerOperand(),
                                            Relations().sle().sge())) {
        if (related.second.has(Relations::EQ))
            continue;

        if (newGraph.are(related.first, Relations::PT, compared)) {
            size_t id = newGraph.getBorderId(related.first);
            if (id == std::string::npos)
                continue;
            auto arg =
                    structure.getBorderValueFor(load->getFunction(), id).from;
            if (newGraph.are(arg, related.second.get(),
                             load->getPointerOperand())) {
                Relations::Type toSet =
                        rel == Relations::EQ
                                ? Relations::EQ
                                : Relations::getStrict(related.second.get());
                newGraph.set(load->getPointerOperand(), toSet, related.first);
            }
        }
    }
}

bool RelationsAnalyzer::processPhi(ValueRelations &newGraph,
                                   VRAssumeBool *assume) {
    const llvm::PHINode *phi = llvm::cast<llvm::PHINode>(assume->getValue());
    const auto &sources =
            structure.possibleSources(phi, assume->getAssumption());
    if (sources.size() != 1)
        return true;

    VRInstruction *inst = static_cast<VRInstruction *>(sources[0]->op.get());
    const auto *icmp = llvm::dyn_cast<llvm::ICmpInst>(inst->getInstruction());

    bool result;
    if (icmp) {
        VRAssumeBool tmp{inst->getInstruction(), assume->getAssumption()};
        result = processICMP(codeGraph.getVRLocation(icmp).relations, newGraph,
                             &tmp);
        if (!result)
            return false;
    }

    VRLocation &source = *sources[0]->target;
    result = newGraph.merge(source.relations);
    assert(result);
    return true;
}

// *********************** merge helpers **************************** //
void RelationsAnalyzer::inferFromPreds(VRLocation &location, Handle lt,
                                       Relations known, Handle rt) {
    const ValueRelations &predGraph = location.getTreePredecessor().relations;
    ValueRelations &newGraph = location.relations;

    std::set<V> setEqual;
    for (const auto *ltVal : predGraph.getEqual(lt)) {
        if (setEqual.find(ltVal) != setEqual.end())
            continue;
        for (const auto *rtVal : predGraph.getEqual(rt)) {
            if (ltVal == rtVal)
                continue;

            Relations related = getCommon(location, ltVal, known, rtVal);
            if (!related.any())
                continue;

            if (related.has(Relations::EQ))
                setEqual.emplace(rtVal);
            newGraph.set(ltVal, related, rtVal);
        }

        size_t rtId = predGraph.getBorderId(rt);
        if (rtId != std::string::npos) {
            Relations related = getCommon(location, ltVal, known, rtId);
            if (!related.any())
                continue;

            newGraph.set(ltVal, related, rtId);
        }
    }

    size_t ltId = predGraph.getBorderId(lt);
    if (ltId != std::string::npos) {
        for (const auto *rtVal : predGraph.getEqual(rt)) {
            Relations related = getCommon(location, ltId, known, rtVal);
            if (!related.any())
                continue;

            newGraph.set(ltId, related, rtVal);
        }

        size_t rtId = predGraph.getBorderId(rt);
        if (rtId != std::string::npos) {
            Relations related = getCommon(location, ltId, known, rtId);
            if (!related.any())
                return;

            newGraph.set(ltId, related, rtId);
        }
    }
}

std::vector<const VRLocation *>
RelationsAnalyzer::getBranchChangeLocations(const VRLocation &join,
                                            const VectorSet<V> &froms) const {
    std::vector<const VRLocation *> changeLocations;
    for (unsigned i = 0; i < join.predsSize(); ++i) {
        auto loc = join.getPredLocation(i);
        bool hasLoad = false;
        for (V from : froms) {
            if (loc->relations.hasLoad(from)) {
                hasLoad = true;
                break;
            }
        }
        if (!hasLoad)
            return {};
        changeLocations.emplace_back(loc);
    }
    return changeLocations;
}

std::vector<const VRLocation *>
RelationsAnalyzer::getLoopChangeLocations(const VRLocation &join,
                                          const VectorSet<V> &froms) const {
    std::vector<const VRLocation *> changeLocations = {
            &join.getTreePredecessor()};

    for (const auto &inloopInst : structure.getInloopValues(join)) {
        VRLocation &targetLoc =
                *codeGraph.getVRLocation(inloopInst).getSuccLocation(0);

        for (V from : froms) {
            if (mayOverwrite(inloopInst, from)) {
                if (!targetLoc.relations.hasLoad(from))
                    return {}; // no merge by load can happen here

                changeLocations.emplace_back(&targetLoc);
            }
        }
    }
    return changeLocations;
}

std::vector<const VRLocation *>
RelationsAnalyzer::getChangeLocations(const VRLocation &join,
                                      const VectorSet<V> &froms) {
    if (!join.isJustLoopJoin() && !join.isJustBranchJoin())
        return {};
    if (join.isJustBranchJoin()) {
        return getBranchChangeLocations(join, froms);
    }
    assert(join.isJustLoopJoin());
    return getLoopChangeLocations(join, froms);
}

std::pair<RelationsAnalyzer::C, Relations>
RelationsAnalyzer::getBoundOnPointedToValue(
        const std::vector<const VRLocation *> &changeLocations,
        const VectorSet<V> &froms, Relation rel) {
    C bound = nullptr;
    Relations current = allRelations;

    for (const VRLocation *loc : changeLocations) {
        const ValueRelations &graph = loc->relations;
        HandlePtr from = getCorrespondingByContent(graph, froms);
        assert(from);
        if (!graph.hasLoad(*from))
            return {nullptr, current};

        Handle pointedTo = graph.getPointedTo(*from);
        auto valueRels = graph.getBound(pointedTo, rel);

        if (!valueRels.first)
            return {nullptr, current};

        if (!bound || ValueRelations::compare(bound, Relations::getStrict(rel),
                                              valueRels.first)) {
            bound = valueRels.first;
            current = Relations().set(Relations::getStrict(rel)).addImplied();
        }

        current &= valueRels.second;
        assert(current.any());
    }
    return {bound, current};
}

std::pair<V, bool> getCompared(const ValueRelations &graph,
                               const llvm::ICmpInst *icmp,
                               const llvm::Value *from) {
    const auto *op1 = icmp->getOperand(0);
    const auto *op2 = icmp->getOperand(1);

    for (const auto *op : {op1, op2}) {
        const auto &froms = RelationsAnalyzer::getFroms(graph, op);
        if (std::find(froms.begin(), froms.end(), from) != froms.end()) {
            if (op == op1)
                return {op2, froms.size() <= 1};
            return {op1, froms.size() <= 1};
        }
    }
    return {nullptr, false};
}

std::vector<const llvm::ICmpInst *>
RelationsAnalyzer::getEQICmp(const VRLocation &join) {
    std::vector<const llvm::ICmpInst *> result;
    for (const auto *loopEnd : join.loopEnds) {
        if (!loopEnd->op->isAssumeBool())
            continue;

        const auto *assume = static_cast<VRAssumeBool *>(loopEnd->op.get());
        const auto &icmps = structure.getRelevantConditions(assume);
        if (icmps.empty())
            return {};

        for (const auto *icmp : icmps) {
            Relation rel = ICMPToRel(icmp, assume->getAssumption());

            if (rel != Relations::EQ)
                continue; // TODO check or collect

            result.emplace_back(icmp);
        }
    }
    return result;
}

void RelationsAnalyzer::inferFromNonEquality(VRLocation &join,
                                             const VectorSet<V> &froms, Shift s,
                                             Handle placeholder) {
    const ValueRelations &predGraph = join.getTreePredecessor().relations;
    for (V from : froms) {
        Handle initH = predGraph.getPointedTo(from);
        for (const auto *icmp : getEQICmp(join)) {
            V compared;
            bool direct;
            std::tie(compared, direct) = getCompared(
                    codeGraph.getVRLocation(icmp).relations, icmp, from);
            if (!compared ||
                (!llvm::isa<llvm::Constant>(compared) &&
                 !codeGraph.getVRLocation(icmp)
                          .relations.getInstance<llvm::Argument>(compared)))
                continue;

            const llvm::Argument *arg = getArgument(predGraph, initH);
            if (!arg)
                continue;

            const llvm::Function *func = icmp->getFunction();

            ValueRelations &entryRels =
                    codeGraph.getEntryLocation(*func).relations;
            if (direct) {
                if (!join.relations.are(*predGraph.getEqual(initH).begin(),
                                        s == Shift::INC ? Relations::SLE
                                                        : Relations::SGE,
                                        compared)) {
                    structure.addPrecondition(func, arg,
                                              s == Shift::INC ? Relations::SLE
                                                              : Relations::SGE,
                                              compared);
                    entryRels.set(arg,
                                  s == Shift::INC ? Relations::SLE
                                                  : Relations::SGE,
                                  compared);
                }

                if (join.relations.are(arg, Relations::NE, compared))
                    join.relations.set(placeholder,
                                       s == Shift::INC ? Relations::SLT
                                                       : Relations::SGT,
                                       compared);
                else
                    join.relations.set(placeholder,
                                       s == Shift::INC ? Relations::SLE
                                                       : Relations::SGE,
                                       compared);
            } else {
                if (structure.hasBorderValues(func)) {
                    for (const auto &borderVal :
                         structure.getBorderValuesFor(func)) {
                        if (borderVal.from == arg &&
                            borderVal.stored == compared) {
                            auto thisBorderPlaceholder =
                                    join.relations.getBorderH(borderVal.id);
                            assert(thisBorderPlaceholder);
                            join.relations.set(placeholder,
                                               s == Shift::INC ? Relations::SLE
                                                               : Relations::SGE,
                                               *thisBorderPlaceholder);
                            return;
                        }
                    }
                }

                auto id = structure.addBorderValue(func, arg, compared);
                Handle entryBorderPlaceholder = entryRels.newBorderBucket(id);
                entryRels.set(entryBorderPlaceholder, Relations::PT, compared);
                entryRels.set(entryBorderPlaceholder,
                              Relations::inverted(s == Shift::INC
                                                          ? Relations::SLE
                                                          : Relations::SGE),
                              arg);
            }
        }
    }
}

void RelationsAnalyzer::inferShiftInLoop(
        const std::vector<const VRLocation *> &changeLocations,
        const VectorSet<V> &froms, ValueRelations &newGraph,
        Handle placeholder) {
    const ValueRelations &predGraph = changeLocations[0]->relations;
    HandlePtr from = getCorrespondingByContent(predGraph, froms);
    assert(from);

    const auto &initial = predGraph.getEqual(predGraph.getPointedTo(*from));
    if (initial.empty())
        return;

    auto shift = getShift(changeLocations, froms);
    if (shift == Shift::UNKNOWN)
        return;

    if (shift == Shift::INC || shift == Shift::DEC)
        inferFromNonEquality(*changeLocations[0]->getSuccLocation(0), froms,
                             shift, placeholder);

    Relations::Type rel =
            shift == Shift::EQ
                    ? Relations::EQ
                    : (shift == Shift::INC ? Relations::SLE : Relations::SGE);

    // placeholder must be first so that if setting EQ, its bucket is
    // preserved
    newGraph.set(placeholder, Relations::inverted(rel), *initial.begin());
}

void RelationsAnalyzer::relateBounds(
        const std::vector<const VRLocation *> &changeLocations,
        const VectorSet<V> &froms, ValueRelations &newGraph,
        Handle placeholder) {
    auto signedLowerBound =
            getBoundOnPointedToValue(changeLocations, froms, Relation::SGE);
    auto unsignedLowerBound = getBoundOnPointedToValue(
            changeLocations, froms,
            Relation::UGE); // TODO collect upper bound too

    if (signedLowerBound.first)
        newGraph.set(placeholder, signedLowerBound.second,
                     signedLowerBound.first);

    if (unsignedLowerBound.first)
        newGraph.set(placeholder, unsignedLowerBound.second,
                     unsignedLowerBound.first);
}

void RelationsAnalyzer::relateValues(
        const std::vector<const VRLocation *> &changeLocations,
        const VectorSet<V> &froms, ValueRelations &newGraph,
        Handle placeholder) {
    const ValueRelations &predGraph = changeLocations[0]->relations;
    HandlePtr from = getCorrespondingByContent(predGraph, froms);
    assert(from);
    Handle pointedTo = predGraph.getPointedTo(*from);

    for (auto pair : predGraph.getRelated(pointedTo, comparative)) {
        Handle relatedH = pair.first;
        Relations relations = pair.second;

        assert(predGraph.are(pointedTo, relations, relatedH));

        if (relatedH == pointedTo && !predGraph.getEqual(relatedH).empty())
            continue;

        for (V related : predGraph.getEqual(relatedH)) {
            Relations common = getCommonByPointedTo(froms, changeLocations,
                                                    related, relations);
            if (common.any())
                newGraph.set(placeholder, common, related);
        }

        size_t mBorderId = predGraph.getBorderId(relatedH);
        if (mBorderId != std::string::npos) {
            Relations common = getCommonByPointedTo(froms, changeLocations,
                                                    mBorderId, relations);

            if (common.any()) {
                auto borderH = newGraph.getBorderH(mBorderId);
                if (!borderH)
                    borderH = &newGraph.newBorderBucket(mBorderId);
                newGraph.set(placeholder, common, *borderH);
            }
        }
    }
}

// **************************** merge ******************************* //
void RelationsAnalyzer::mergeRelations(VRLocation &location) {
    assert(location.predsSize() > 1);

    const ValueRelations &predGraph = location.getTreePredecessor().relations;

    for (const auto &bucketVal : predGraph.getBucketToVals()) {
        for (const auto &related :
             predGraph.getRelated(bucketVal.first, restricted)) {
            inferFromPreds(location, bucketVal.first, related.second,
                           related.first);
        }
    }

    ValueRelations &thisGraph = location.relations;

    // merge relations from tree predecessor only
    if (location.isJustLoopJoin()) {
        __attribute__((unused)) bool result =
                thisGraph.merge(predGraph, comparative);
        assert(result);
    }
}

void RelationsAnalyzer::mergeRelationsByPointedTo(VRLocation &loc) {
    ValueRelations &newGraph = loc.relations;
    ValueRelations &predGraph = loc.getTreePredecessor().relations;

    for (auto it = predGraph.begin_buckets(Relations().pt());
         it != predGraph.end_buckets(); ++it) {
        const VectorSet<V> &froms = predGraph.getEqual(it->from());
        if (!froms.empty()) {
            std::vector<const VRLocation *> changeLocations =
                    getChangeLocations(loc, froms);

            if (changeLocations.empty())
                continue;

            Handle placeholder = newGraph.newPlaceholderBucket(*froms.begin());

            if (loc.isJustLoopJoin())
                inferShiftInLoop(changeLocations, froms, newGraph, placeholder);
            relateBounds(changeLocations, froms, newGraph, placeholder);
            relateValues(changeLocations, froms, newGraph, placeholder);

            if (!newGraph.getEqual(placeholder).empty() ||
                newGraph.hasAnyRelation(placeholder))
                newGraph.setLoad(*froms.begin(), placeholder);
            else
                newGraph.erasePlaceholderBucket(placeholder);
        }

        if (froms.empty()) {
            V arg = getArgument(predGraph, it->from());
            if (!arg)
                continue;
            std::vector<const VRLocation *> changeLocations =
                    getChangeLocations(loc, {arg});

            if (changeLocations.size() == 1) {
                Relations between = predGraph.between(arg, it->from());
                assert(!between.has(Relations::EQ));
                size_t id = predGraph.getBorderId(it->from());
                if (id == std::string::npos)
                    continue;
                auto borderH = newGraph.getBorderH(id);
                if (!borderH)
                    borderH = &newGraph.newBorderBucket(id);

                newGraph.set(arg, between, *borderH);
                for (V to : predGraph.getEqual(it->to()))
                    newGraph.set(*borderH, Relations::PT, to);
            }
        }
    }
}

// ***************************** edge ******************************* //
void RelationsAnalyzer::processInstruction(ValueRelations &graph, I inst) {
    switch (inst->getOpcode()) {
    case llvm::Instruction::Store:
        return storeGen(graph, llvm::cast<llvm::StoreInst>(inst));
    case llvm::Instruction::Load:
        return loadGen(graph, llvm::cast<llvm::LoadInst>(inst));
    case llvm::Instruction::GetElementPtr:
        return gepGen(graph, llvm::cast<llvm::GetElementPtrInst>(inst));
    case llvm::Instruction::ZExt:
    case llvm::Instruction::SExt: // (S)ZExt should not change value
        return extGen(graph, llvm::cast<llvm::CastInst>(inst));
    case llvm::Instruction::Add:
    case llvm::Instruction::Sub:
    case llvm::Instruction::Mul:
        return opGen(graph, llvm::cast<llvm::BinaryOperator>(inst));
    case llvm::Instruction::SRem:
    case llvm::Instruction::URem:
        return remGen(graph, llvm::cast<llvm::BinaryOperator>(inst));
    default:
        if (const auto *cast = llvm::dyn_cast<llvm::CastInst>(inst)) {
            return castGen(graph, cast);
        }
    }
}

void RelationsAnalyzer::rememberValidated(const ValueRelations &prev,
                                          ValueRelations &graph, I inst) const {
    assert(&prev == &codeGraph.getVRLocation(inst).relations);

    for (auto it = prev.begin_buckets(Relations().pt());
         it != prev.end_buckets(); ++it) {
        for (V from : prev.getEqual(it->from())) {
            if (!mayOverwrite(inst, from)) {
                for (V to : prev.getEqual(it->to()))
                    graph.set(from, Relations::PT, to);
            }
            if (const auto *store = llvm::dyn_cast<llvm::StoreInst>(inst)) {
                if (prev.are(it->to(), Relations::EQ,
                             store->getValueOperand())) {
                    for (V to : prev.getEqual(it->to()))
                        graph.set(from, Relations::PT, to);
                }
            }
        }

        if (prev.getEqual(it->from()).empty() &&
            !it->from().hasRelation(Relations::PF)) {
            V arg = getArgument(prev, it->from());
            if (arg && !mayOverwrite(inst, arg)) {
                auto mH = graph.getBorderH(prev.getBorderId(it->from()));
                assert(mH);

                for (V to : prev.getEqual(it->to()))
                    graph.set(*mH, Relations::PT, to);
            }
        }
    }
}

bool RelationsAnalyzer::processAssumeBool(const ValueRelations &oldGraph,
                                          ValueRelations &newGraph,
                                          VRAssumeBool *assume) {
    if (llvm::isa<llvm::ICmpInst>(assume->getValue()))
        return processICMP(oldGraph, newGraph, assume);
    if (llvm::isa<llvm::PHINode>(assume->getValue()))
        return processPhi(newGraph, assume);
    return false; // TODO; probably call
}

bool RelationsAnalyzer::processAssumeEqual(const ValueRelations &oldGraph,
                                           ValueRelations &newGraph,
                                           VRAssumeEqual *assume) {
    V val1 = assume->getValue();
    V val2 = assume->getAssumption();
    if (oldGraph.hasConflictingRelation(val1, val2, Relation::EQ))
        return false;
    newGraph.setEqual(val1, val2);
    return true;
}

// ************************* topmost ******************************* //
void RelationsAnalyzer::processOperation(VRLocation *source, VRLocation *target,
                                         VROp *op) {
    if (!target)
        return;
    assert(source && target && op);

    ValueRelations &newGraph = target->relations;

    if (op->isInstruction()) {
        newGraph.merge(source->relations, comparative);
        I inst = static_cast<VRInstruction *>(op)->getInstruction();
        rememberValidated(source->relations, newGraph, inst);
        processInstruction(newGraph, inst);

    } else if (op->isAssume()) {
        bool shouldMerge;
        if (op->isAssumeBool())
            shouldMerge = processAssumeBool(source->relations, newGraph,
                                            static_cast<VRAssumeBool *>(op));
        else // isAssumeEqual
            shouldMerge = processAssumeEqual(source->relations, newGraph,
                                             static_cast<VRAssumeEqual *>(op));
        if (shouldMerge) {
            __attribute__((unused)) bool result =
                    newGraph.merge(source->relations);
            assert(result);
        }

        if (op->isAssumeBool())
            inferFromNEPointers(newGraph, static_cast<VRAssumeBool *>(op));
    } else { // else op is noop
        newGraph.merge(source->relations, allRelations);
    }
}

bool RelationsAnalyzer::passFunction(const llvm::Function &function,
                                     __attribute__((unused)) bool print) {
    bool changed = false;

    for (auto it = codeGraph.lazy_dfs_begin(function);
         it != codeGraph.lazy_dfs_end(); ++it) {
        VRLocation &location = *it;
#ifndef NDEBUG
        const bool cond = location.id == 91;
        if (print && cond) {
            std::cerr << "LOCATION " << location.id << "\n";
            for (unsigned i = 0; i < location.predsSize(); ++i) {
                std::cerr << "pred" << i << " "
                          << location.getPredEdge(i)->op->toStr() << "\n";
                std::cerr << location.getPredLocation(i)->relations << "\n";
            }
            std::cerr << "before\n" << location.relations << "\n";
            std::cerr << "inside\n";
        }
#endif

        if (location.predsSize() > 1) {
            mergeRelations(location);
            mergeRelationsByPointedTo(location);
        } else if (location.predsSize() == 1) {
            VREdge *edge = location.getPredEdge(0);
            processOperation(edge->source, edge->target, edge->op.get());
        } // else no predecessors => nothing to be passed

        bool locationChanged = location.relations.unsetChanged();
#ifndef NDEBUG
        if (print && cond) {
            std::cerr << "after\n";
            if (locationChanged)
                std::cerr << location.relations;
            // return false;
        }
#endif
        changed |= locationChanged;
    }
    return changed;
}

unsigned RelationsAnalyzer::analyze(unsigned maxPass) {
    unsigned maxExecutedPass = 0;

    for (const auto &function : module) {
        if (function.isDeclaration())
            continue;

        bool changed = true;
        unsigned passNum = 0;
        while (changed && passNum < maxPass) {
            changed = passFunction(function, false); // passNum + 1 == maxPass);
            ++passNum;
        }

        maxExecutedPass = std::max(maxExecutedPass, passNum);
    }

    return maxExecutedPass;
}

std::vector<V> RelationsAnalyzer::getFroms(const ValueRelations &rels, V val) {
    std::vector<V> result;
    const auto *load = rels.getInstance<llvm::LoadInst>(val);
    const auto *mH = rels.getHandle(val);

    while (load || (mH && rels.has(*mH, Relations::PF))) {
        if (load) {
            val = load->getPointerOperand();
            mH = rels.getHandle(val);
            load = rels.getInstance<llvm::LoadInst>(val);
            result.emplace_back(val);
        } else {
            const auto &pointedFrom = rels.getRelated(val, Relations().pf());
            if (pointedFrom.size() != 1)
                return result;
            mH = &pointedFrom.begin()->first.get();
            load = rels.getInstance<llvm::LoadInst>(*mH);
            if (load)
                result.emplace_back(load);
            else if (const auto *gep =
                             rels.getInstance<llvm::GetElementPtrInst>(*mH))
                result.emplace_back(gep);
            else {
                const auto &eqvals = rels.getEqual(*mH);
                if (eqvals.empty())
                    return result;
                result.emplace_back(*eqvals.begin());
            }
        }
    }

    return result;
}

RelationsAnalyzer::HandlePtr
RelationsAnalyzer::getHandleFromFroms(const ValueRelations &rels,
                                      const std::vector<V> &froms) {
    if (froms.empty())
        return nullptr;
    auto *from = rels.getHandle(froms.back());
    for (unsigned i = 0; i < froms.size(); ++i) {
        if (!from || !rels.has(*from, Relations::PT))
            return nullptr;
        from = &rels.getPointedTo(*from);
    }
    return from;
}

RelationsAnalyzer::HandlePtr
RelationsAnalyzer::getHandleFromFroms(const ValueRelations &toRels,
                                      const ValueRelations &fromRels, V val) {
    auto froms = getFroms(fromRels, val);
    auto to = getHandleFromFroms(toRels, froms);
    return to;
}

RelationsAnalyzer::HandlePtr
RelationsAnalyzer::getCorrespondingByContent(const ValueRelations &toRels,
                                             const ValueRelations &fromRels,
                                             Handle h) {
    return getCorrespondingByContent(toRels, fromRels.getEqual(h));
}

RelationsAnalyzer::HandlePtr
RelationsAnalyzer::getCorrespondingByContent(const ValueRelations &toRels,
                                             const VectorSet<V> &vals) {
    HandlePtr result = nullptr;
    for (const auto *val : vals) {
        auto *mThisH = toRels.getHandle(val);
        if (!mThisH)
            continue;
        if (result && result != mThisH)
            return nullptr;
        result = mThisH;
    }
    return result;
}

RelationsAnalyzer::HandlePtr
RelationsAnalyzer::getCorrespondingByFrom(const ValueRelations &toRels,
                                          const ValueRelations &fromRels,
                                          Handle h) {
    const auto &froms = fromRels.getRelated(h, Relations().pf());
    if (froms.size() != 1)
        return nullptr;

    const auto &fromFromH = froms.begin()->first;
    const auto *toFromH =
            getCorrespondingByContent(toRels, fromRels, fromFromH);
    if (!toFromH)
        return nullptr;

    if (!toRels.has(*toFromH, Relations::PT))
        return nullptr;

    return &toRels.getPointedTo(*toFromH);
}

const llvm::AllocaInst *RelationsAnalyzer::getOrigin(const ValueRelations &rels,
                                                     V val) {
    for (const auto &related : rels.getRelated(val, Relations().sge())) {
        if (const auto *alloca =
                    rels.getInstance<llvm::AllocaInst>(related.first.get())) {
            return alloca;
        }
    }
    return nullptr;
}

} // namespace vr
} // namespace dg
