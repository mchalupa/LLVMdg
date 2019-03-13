#include <set>
#include <cassert>

// ignore unused parameters in LLVM libraries
#if (__clang__)
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wunused-parameter"
#else
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-parameter"
#endif

#include <llvm/Config/llvm-config.h>
#if ((LLVM_VERSION_MAJOR == 3) && (LLVM_VERSION_MINOR < 5))
 #include <llvm/Support/CFG.h>
#else
 #include <llvm/IR/CFG.h>
#endif

#include <llvm/IR/Instruction.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/DataLayout.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Constant.h>
#include <llvm/Support/raw_os_ostream.h>

#if (__clang__)
#pragma clang diagnostic pop // ignore -Wunused-parameter
#else
#pragma GCC diagnostic pop
#endif


#include "dg/llvm/analysis/PointsTo/PointerSubgraph.h"

#include "llvm/analysis/ReachingDefinitions/LLVMRDBuilderDense.h"
#include "llvm/llvm-utils.h"

namespace dg {
namespace analysis {
namespace rd {

RDNode *LLVMRDBuilderDense::createAlloc(const llvm::Instruction *Inst)
{
    RDNode *node = new RDNode(RDNodeType::ALLOC);
    addNode(Inst, node);

    if (const llvm::AllocaInst *AI
            = llvm::dyn_cast<llvm::AllocaInst>(Inst))
        node->setSize(getAllocatedSize(AI, DL));

    return node;
}

RDNode *LLVMRDBuilderDense::createDynAlloc(const llvm::Instruction *Inst, AllocationFunction type)
{
    using namespace llvm;

    RDNode *node = new RDNode(RDNodeType::DYN_ALLOC);
    addNode(Inst, node);

    const CallInst *CInst = cast<CallInst>(Inst);
    const Value *op;
    uint64_t size = 0, size2 = 0;

    switch (type) {
        case AllocationFunction::MALLOC:
        case AllocationFunction::ALLOCA:
            op = CInst->getOperand(0);
            break;
        case AllocationFunction::CALLOC:
            op = CInst->getOperand(1);
            break;
        default:
            errs() << *CInst << "\n";
            assert(0 && "unknown memory allocation type");
            // for NDEBUG
            abort();
    };

    // infer allocated size
    size = getConstantValue(op);
    if (size != 0 && type == AllocationFunction::CALLOC) {
        // if this is call to calloc, the size is given
        // in the first argument too
        size2 = getConstantValue(CInst->getOperand(0));
        if (size2 != 0)
            size *= size2;
    }

    node->setSize(size);
    return node;
}

RDNode *LLVMRDBuilderDense::createRealloc(const llvm::Instruction *Inst)
{
    RDNode *node = new RDNode(RDNodeType::DYN_ALLOC);
    addNode(Inst, node);

    uint64_t size = getConstantValue(Inst->getOperand(1));
    if (size == 0)
        size = Offset::UNKNOWN;
    else
        node->setSize(size);

    // realloc defines itself, since it copies the values
    // from previous memory
    node->addDef(node, 0, size, false /* strong update */);

    return node;
}

static void getLocalVariables(const llvm::Function *F,
                              std::set<const llvm::Value *>& ret)
{
    using namespace llvm;

    // get all alloca insts that are not address taken
    // (are not stored into a pointer)
    // -- that means that they can not be used outside of
    // this function
    for (const BasicBlock& block : *F) {
        for (const Instruction& Inst : block) {
            if (isa<AllocaInst>(&Inst)) {
                bool is_address_taken = false;
                for (auto I = Inst.use_begin(), E = Inst.use_end();
                     I != E; ++I) {
#if ((LLVM_VERSION_MAJOR == 3) && (LLVM_VERSION_MINOR < 5))
                    const llvm::Value *use = *I;
#else
                    const llvm::Value *use = I->getUser();
#endif
                    const StoreInst *SI = dyn_cast<StoreInst>(use);
                    // is the value operand our alloca?
                    if (SI && SI->getValueOperand() == &Inst) {
                        is_address_taken = true;
                        break;
                    }
                }

                if (!is_address_taken)
                    ret.insert(&Inst);
            }
        }
    }
}

RDNode *LLVMRDBuilderDense::createReturn(const llvm::Instruction *Inst)
{
    RDNode *node = new RDNode(RDNodeType::RETURN);
    addNode(Inst, node);

    // FIXME: don't do that for every return instruction,
    // compute it only once for a function
    std::set<const llvm::Value *> locals;
    getLocalVariables(Inst->getParent()->getParent(),
                      locals);

    for (const llvm::Value *ptrVal : locals) {
        RDNode *ptrNode = getOperand(ptrVal);
        if (!ptrNode) {
            llvm::errs() << *ptrVal << "\n";
            llvm::errs() << "Don't have created node for local variable\n";
            abort();
        }

        // make this return node behave like we overwrite the definitions.
        // We actually don't override them, therefore they are dropped
        // and that is what we want (we don't want to propagade
        // local definitions from functions into callees)
        node->addOverwrites(ptrNode, 0, Offset::UNKNOWN);
    }

    return node;
}

RDNode *LLVMRDBuilderDense::getOperand(const llvm::Value *val)
{
    RDNode *op = getNode(val);
    if (!op)
        return createNode(*llvm::cast<llvm::Instruction>(val));

    return op;
}

RDNode *LLVMRDBuilderDense::createNode(const llvm::Instruction &Inst)
{
    using namespace llvm;

    RDNode *node = nullptr;
    switch(Inst.getOpcode()) {
        case Instruction::Alloca:
            // we need alloca's as target to DefSites
            node = createAlloc(&Inst);
            break;
        case Instruction::Call:
            node = createCall(&Inst)[0].returnNode;
            break;
        default:
            llvm::errs() << "BUG: " << Inst << "\n";
            abort();
    }

    return node;
}

RDNode *LLVMRDBuilderDense::createStore(const llvm::Instruction *Inst)
{
    RDNode *node = new RDNode(RDNodeType::STORE);
    addNode(Inst, node);

    uint64_t size = getAllocatedSize(Inst->getOperand(0)->getType(), DL);
    if (size == 0)
        size = Offset::UNKNOWN;

    auto defSites = mapPointers(Inst, Inst->getOperand(1), size);

    // strong update is possible only with must aliases. Also we can not
    // be pointing to heap, because then we don't know which object it
    // is in run-time, like:
    //  void *foo(int a)
    //  {
    //      void *mem = malloc(...)
    //      mem->n = a;
    //  }
    //
    //  1. mem1 = foo(3);
    //  2. mem2 = foo(4);
    //  3. assert(mem1->n == 3);
    //
    //  If we would do strong update on line 2 (which we would, since
    //  there we have must alias for the malloc), we would loose the
    //  definitions for line 1 and we would get incorrect results
    bool strong_update = false;
    if (defSites.size() == 1) {
        const auto& ds = *(defSites.begin());
        strong_update = !ds.offset.isUnknown() && !ds.len.isUnknown() &&
                         ds.target->getType() != RDNodeType::DYN_ALLOC;
    }

    for (const auto& ds : defSites) {
        node->addDef(ds, strong_update);
    }

    assert(node);
    return node;
}

RDNode *LLVMRDBuilderDense::createLoad(const llvm::Instruction *Inst)
{
    RDNode *node = new RDNode(RDNodeType::LOAD);
    addNode(Inst, node);

    uint64_t size = getAllocatedSize(Inst->getType(), DL);
    if (size == 0)
        size = Offset::UNKNOWN;

    auto defSites = mapPointers(Inst, Inst->getOperand(0), size);
    for (const auto& ds : defSites) {
        node->addUse(ds);
    }

    assert(node);
    return node;
}

template <typename OptsT>
static bool isRelevantCall(const llvm::Instruction *Inst,
                           OptsT& opts)
{
    using namespace llvm;

    // we don't care about debugging stuff
    if (isa<DbgValueInst>(Inst))
        return false;

    const CallInst *CInst = cast<CallInst>(Inst);
    const Value *calledVal = CInst->getCalledValue()->stripPointerCasts();
    const Function *func = dyn_cast<Function>(calledVal);

    if (!func)
        // function pointer call - we need that
        return true;

    if (func->size() == 0) {
        // we have a model for this function
        if (opts.getFunctionModel(func->getName()))
            return true;
        // memory allocation
        if (opts.isAllocationFunction(func->getName()))
            return true;

        if (func->isIntrinsic()) {
            switch (func->getIntrinsicID()) {
                case Intrinsic::memmove:
                case Intrinsic::memcpy:
                case Intrinsic::memset:
                case Intrinsic::vastart:
                    return true;
                default:
                    return false;
            }
        }

        // undefined function
        return true;
    } else
        // we want defined function, since those can contain
        // pointer's manipulation and modify CFG
        return true;

    assert(0 && "We should not reach this");
}

static inline void makeEdge(RDNode *src, RDNode *dst)
{
    assert(src != dst && "Tried creating self-loop");
    assert(src != nullptr);
    // This is checked by addSuccessor():
    // assert(dst != nullptr);

    src->addSuccessor(dst);
}

// return first and last nodes of the block
std::pair<RDNode *, RDNode *>
LLVMRDBuilderDense::buildBlock(const llvm::BasicBlock& block)
{
    using namespace llvm;

    // the first node is dummy and serves as a phi from previous
    // blocks so that we can have proper mapping
    RDNode *node = new RDNode(RDNodeType::PHI);
    RDNode *last_node = node;

    addNode(node);
    std::pair<RDNode *, RDNode *> ret(node, nullptr);

    for (const Instruction& Inst : block) {
        node = getNode(&Inst);
        if (!node) {
           switch(Inst.getOpcode()) {
                case Instruction::Alloca:
                    // we need alloca's as target to DefSites
                    node = createAlloc(&Inst);
                    break;
                case Instruction::Store:
                    node = createStore(&Inst);
                    break;
                case Instruction::Load:
                    if (buildUses)
                        node = createLoad(&Inst);
                    break;
                case Instruction::Ret:
                    // we need create returns, since
                    // these modify CFG and thus data-flow
                    // FIXME: add new type of node NOOP,
                    // and optimize it away later
                    node = createReturn(&Inst);
                    break;
                case Instruction::Call:
                    if (!isRelevantCall(&Inst, _options))
                        break;

                    connectCallsToGraph(&Inst,
                                        createCall(&Inst),
                                        last_node);
                    node = last_node;
            }
        }

        // last_node should never be null
        assert(last_node != nullptr && "BUG: Last node is null");

        // we either created a new node or reused some old node,
        // or node is nullptr (if we haven't created or found anything)
        // if we created a new node, add successor
        if (node && last_node != node) {
            makeEdge(last_node, node);
            last_node = node;
        }

        // reaching definitions for this Inst are contained
        // in the last created node
        addMapping(&Inst, last_node);
    }

    // last node
    ret.second = last_node;

    return ret;
}

static size_t blockAddSuccessors(std::map<const llvm::BasicBlock *,
                                          std::pair<RDNode *, RDNode *>>& built_blocks,
                                 std::pair<RDNode *, RDNode *>& ptan,
                                 const llvm::BasicBlock& block)
{
    size_t num = 0;

    for (llvm::succ_const_iterator
         S = llvm::succ_begin(&block), SE = llvm::succ_end(&block); S != SE; ++S) {
        std::pair<RDNode *, RDNode *>& succ = built_blocks[*S];
        assert((succ.first && succ.second) || (!succ.first && !succ.second));
        if (!succ.first) {
            // if we don't have this block built (there was no points-to
            // relevant instruction), we must pretend to be there for
            // control flow information. Thus instead of adding it as
            // successor, add its successors as successors
            num += blockAddSuccessors(built_blocks, ptan, *(*S));
        } else {
            // add successor to the last nodes
            if (ptan.second != succ.first)
                makeEdge(ptan.second, succ.first);
            ++num;
        }
    }

    return num;
}

LLVMRDBuilderDense::FunctionCall LLVMRDBuilderDense::createCallToFunction(const llvm::Function *F)
{
    RDNode *callNode, *returnNode;

    // dummy nodes for easy generation
    callNode = new RDNode(RDNodeType::CALL);
    returnNode = new RDNode(RDNodeType::CALL_RETURN);

    // do not leak the memory of returnNode (the callNode
    // will be added to nodes_map)
    addNode(returnNode);

    // FIXME: if this is an inline assembly call
    // we need to make conservative assumptions
    // about that - assume that every pointer
    // passed to the subprocesdure may be defined on
    // UNKNOWN OFFSET, etc.

    // reuse built subgraphs if available, so that we won't get
    // stuck in infinite loop with recursive functions
    RDNode *root, *ret;
    auto it = subgraphs_map.find(F);
    if (it == subgraphs_map.end()) {
        // create a new subgraph
        std::tie(root, ret) = buildFunction(*F);
    } else {
        root = it->second.root;
        ret = it->second.ret;
    }

    assert(root && ret && "Incomplete subgraph");

    // add an edge from last argument to root of the subgraph
    // and from the subprocedure return node (which is one - unified
    // for all return nodes) to return from the call
    makeEdge(callNode, root);
    makeEdge(ret, returnNode);

    return {callNode, returnNode, CallType::PLAIN_CALL};
}

std::pair<RDNode *, RDNode *>
LLVMRDBuilderDense::buildFunction(const llvm::Function& F)
{
    // here we'll keep first and last nodes of every built block and
    // connected together according to successors
    std::map<const llvm::BasicBlock *, std::pair<RDNode *, RDNode *>> built_blocks;

    // create root and (unified) return nodes of this subgraph. These are
    // just for our convenience when building the graph, they can be
    // optimized away later since they are noops
    RDNode *root = new RDNode(RDNodeType::NOOP);
    RDNode *ret = new RDNode(RDNodeType::NOOP);

    // emplace new subgraph to avoid looping with recursive functions
    subgraphs_map.emplace(&F, Subgraph(root, ret));

    RDNode *first = nullptr;
    for (const llvm::BasicBlock& block : F) {
        std::pair<RDNode *, RDNode *> nds = buildBlock(block);
        assert(nds.first && nds.second);

        built_blocks[&block] = nds;
        if (!first)
            first = nds.first;
    }

    assert(first);
    makeEdge(root, first);

    std::vector<RDNode *> rets;
    for (const llvm::BasicBlock& block : F) {
        auto it = built_blocks.find(&block);
        if (it == built_blocks.end())
            continue;

        std::pair<RDNode *, RDNode *>& ptan = it->second;
        assert((ptan.first && ptan.second) || (!ptan.first && !ptan.second));
        if (!ptan.first)
            continue;

        // add successors to this block (skipping the empty blocks)
        // FIXME: this function is shared with PSS, factor it out
        size_t succ_num = blockAddSuccessors(built_blocks, ptan, block);

        // if we have not added any successor, then the last node
        // of this block is a return node
        if (succ_num == 0 && ptan.second->getType() == RDNodeType::RETURN)
            rets.push_back(ptan.second);
    }

    // add successors edges from every real return to our artificial ret node
    for (RDNode *r : rets)
        makeEdge(r, ret);

    return {root, ret};
}

RDNode *LLVMRDBuilderDense::createUndefinedCall(const llvm::CallInst *CInst)
{
    using namespace llvm;

    RDNode *node = new RDNode(RDNodeType::CALL);
    addNode(CInst, node);

    // if we assume that undefined functions are pure
    // (have no side effects), we can bail out here
    if (_options.undefinedArePure)
        return node;

    // every pointer we pass into the undefined call may be defined
    // in the function
    for (unsigned int i = 0; i < CInst->getNumArgOperands(); ++i) {
        const Value *llvmOp = CInst->getArgOperand(i);

        // constants cannot be redefined except for global variables
        // (that are constant, but may point to non constant memory
        const Value *strippedValue = llvmOp->stripPointerCasts();
        if (isa<Constant>(strippedValue)) {
            const GlobalVariable *GV = dyn_cast<GlobalVariable>(strippedValue);
            // if the constant is not global variable,
            // or the global variable points to constant memory
            if (!GV || GV->isConstant())
                continue;
        }

        auto pts = PTA->getLLVMPointsToChecked(llvmOp);
        // if we do not have a pts, this is not pointer
        // relevant instruction. We must do it this way
        // instead of type checking, due to the inttoptr.
        if (!pts.first)
            continue;

        for (const auto& ptr : pts.second) {
            if (llvm::isa<llvm::Function>(ptr.value))
                // function may not be redefined
                continue;

            RDNode *target = getOperand(ptr.value);
            assert(target && "Don't have pointer target for call argument");

            // this call may define this memory
            node->addDef(target, Offset::UNKNOWN, Offset::UNKNOWN);
        }
    }

    // XXX: to be completely correct, we should assume also modification
    // of all global variables, so we should perform a write to
    // unknown memory instead of the loop above

    return node;
}

std::vector<const llvm::Function *>
LLVMRDBuilderDense::getPointsToFunctions(const llvm::Value *calledValue)
{
    using namespace llvm;
    std::vector<const Function *> functions;

    auto pts = PTA->getLLVMPointsToChecked(calledValue);
    if (pts.second.empty()) {
        llvm::errs() << "[RD] error: function pointer with empty points-to set:\n";
        llvm::errs() << *calledValue << "\n";
        return functions;
    }

    for (const auto &pointer : pts.second) {
        if (const auto function = dyn_cast<Function>(pointer.value)) {
            functions.push_back(function);
        }
    }
    return functions;
}

std::vector<const llvm::Function *>
LLVMRDBuilderDense::getPotentialFunctions(const llvm::Instruction *instruction)
{
    using namespace llvm;
    std::vector<const Function *> functions;
    const CallInst *callInstruction = cast<CallInst>(instruction);
    const Value *calledValue = callInstruction->getCalledValue();
    if (isa<Function>(calledValue)) {
        const Function *function = dyn_cast<Function>(calledValue);
        functions.push_back(function);
    } else {
        functions = getPointsToFunctions(calledValue);
    }
    return functions;
}

bool LLVMRDBuilderDense::isInlineAsm(const llvm::Instruction *instruction)
{
    const llvm::CallInst *callInstruction = llvm::cast<llvm::CallInst>(instruction);
    return callInstruction->isInlineAsm();
}

const llvm::Function *
LLVMRDBuilderDense::findFunctionAndRemoveFromVector(std::vector<const llvm::Function *> &functions,
                                                    const std::string& functionName)
{
    using namespace llvm;
    auto it = std::find_if(functions.begin(),
                           functions.end(),
                           [functionName](const Function *function) {
                                return function->getName().str() == functionName;
                           });
    if (it == functions.end()) {
        return nullptr;
    } else {
        const Function *function = *it;
        functions.erase(it);
        return function;
    }
}

void LLVMRDBuilderDense::matchForksAndJoins()
{
    using namespace llvm;
    using namespace pta;
    for (const CallInst *forkInstruction : threadCreateCalls) {
        PSNode *forkPoint = PTA->getPointsTo(forkInstruction->getArgOperand(0));
        for (const CallInst * joinInstruction : threadJoinCalls) {
            std::set<PSNode *> set;
            PSNode *joinPoint = PTA->getPointsTo(joinInstruction->getArgOperand(0))->getOperand(0);
            for (const auto &forkNode : forkPoint->pointsTo) {
                for (const auto &joinNode : joinPoint->pointsTo) {
                    if (joinNode.target == forkNode.target) {
                        set.insert(joinNode.target);
                    }
                }
            }
            if (!set.empty()) {
                auto nodeIterator= nodes_map.find(joinInstruction);
                assert(nodeIterator != nodes_map.end() && "Missing join node in the map");
                RDNode *joinNode = nodeIterator->second;
                std::vector<const Function *> functions;
                auto potentialFunction = forkInstruction->getArgOperand(2);
                if (isa<Function>(potentialFunction)) {
                    functions.push_back(dyn_cast<Function>(potentialFunction));
                } else {
                    functions = getPointsToFunctions(potentialFunction);
                }
                for (const auto &function : functions) {
                    auto graphIterator = subgraphs_map.find(function);
                    assert(graphIterator != subgraphs_map.end() && "Missing function subgraph");
                    RDNode *returnNode = graphIterator->second.ret;
                    makeEdge(returnNode, joinNode);
                }
            }
        }
    }
}

void LLVMRDBuilderDense::connectCallsToGraph(const llvm::Instruction *Inst,
                                             const std::vector<LLVMRDBuilderDense::FunctionCall> &functionCalls,
                                             RDNode *&lastNode)
{
    std::vector<FunctionCall> plainCalls;

    for (const auto& call : functionCalls) {
        if (call.callType == CallType::CREATE_THREAD) {
            makeEdge(lastNode, call.rootNode);
        } else {
            plainCalls.push_back(call);
        }
    }

    RDNode *rootNode = nullptr;
    RDNode *returnNode = nullptr;
    if (plainCalls.size() > 1) {
        rootNode =  new RDNode(RDNodeType::CALL);
        returnNode = new RDNode(RDNodeType::CALL_RETURN);
        addNode(Inst, rootNode);
        addNode(returnNode);
        makeEdge(lastNode, rootNode);
        lastNode = returnNode;
        for (const auto& call : plainCalls) {
            makeEdge(rootNode, call.rootNode);
            makeEdge(call.returnNode, returnNode);
        }
    } else if (!plainCalls.empty()) {
        makeEdge(lastNode, plainCalls[0].rootNode);
        lastNode = plainCalls[0].returnNode;
    }
}

RDNode *LLVMRDBuilderDense::createIntrinsicCall(const llvm::CallInst *CInst)
{
    using namespace llvm;

    const IntrinsicInst *I = cast<IntrinsicInst>(CInst);
    const Value *dest;
    const Value *lenVal;

    RDNode *ret;
    switch (I->getIntrinsicID())
    {
        case Intrinsic::memmove:
        case Intrinsic::memcpy:
        case Intrinsic::memset:
            // memcpy/set <dest>, <src/val>, <len>
            dest = I->getOperand(0);
            lenVal = I->getOperand(2);
            break;
        case Intrinsic::vastart:
            // we create this node because this nodes works
            // as ALLOC in points-to, so we can have
            // reaching definitions to that
            ret = new RDNode(RDNodeType::CALL);
            ret->addDef(ret, 0, Offset::UNKNOWN);
            addNode(CInst, ret);
            return ret;
        default:
            return createUndefinedCall(CInst);
    }

    ret = new RDNode(RDNodeType::CALL);
    addNode(CInst, ret);

    auto pts = PTA->getLLVMPointsToChecked(dest);
    if (!pts.first) {
        llvm::errs() << "[RD] Error: No points-to information for destination in\n";
        llvm::errs() << *I << "\n";
#ifndef NDEBUG
        abort();
#endif
        // continue, the points-to set is {unknown}
    }

    uint64_t len = Offset::UNKNOWN;
    if (const ConstantInt *C = dyn_cast<ConstantInt>(lenVal))
        len = C->getLimitedValue();

    for (const auto& ptr : pts.second) {
        if (llvm::isa<llvm::Function>(ptr.value))
            continue;

        uint64_t from, to;
        if (ptr.offset.isUnknown()) {
            // if the offset is UNKNOWN, use whole memory
            from = Offset::UNKNOWN;
            len = Offset::UNKNOWN;
        } else {
            from = *ptr.offset;
        }

        // do not allow overflow
        if (Offset::UNKNOWN - from > len)
            to = from + len;
        else
            to = Offset::UNKNOWN;

        RDNode *target = getOperand(ptr.value);
        assert(target && "Don't have pointer target for intrinsic call");

        // add the definition
        ret->addDef(target, from, to, true /* strong update */);
    }

    return ret;
}

RDNode *LLVMRDBuilderDense::funcFromModel(const FunctionModel *model, const llvm::CallInst *CInst) {
    RDNode *node = new RDNode(RDNodeType::CALL);
    for (unsigned int i = 0; i < CInst->getNumArgOperands(); ++i) {
        auto defines = model->defines(i);
        if (!defines)
            continue;
        const auto llvmOp = CInst->getArgOperand(i);
        auto pts = PTA->getLLVMPointsToChecked(llvmOp);
        // if we do not have a pts, this is not pointer
        // relevant instruction. We must do it this way
        // instead of type checking, due to the inttoptr.
        if (!pts.first) {
            llvm::errs() << "[Warning]: did not find pt-set for modeled function\n";
            llvm::errs() << "           Func: " << model->name << ", operand " << i << "\n";
            continue;
        }

        for (const auto& ptr : pts.second) {
            if (llvm::isa<llvm::Function>(ptr.value))
                // function may not be redefined
                continue;

            RDNode *target = getOperand(ptr.value);
            assert(target && "Don't have pointer target for call argument");

            auto from = defines->from.isOperand()
                ? getConstantValue(CInst->getArgOperand(defines->from.getOperand())) : defines->from.getOffset();
            auto to = defines->to.isOperand()
                ? getConstantValue(CInst->getArgOperand(defines->to.getOperand())) : defines->to.getOffset();

            // this call may define this memory
            node->addDef(target, from, to);
        }
    }

    return node;
}

std::vector<LLVMRDBuilderDense::FunctionCall>
LLVMRDBuilderDense::createCall(const llvm::Instruction *Inst)
{
    using namespace llvm;
    const CallInst *CInst = cast<CallInst>(Inst);
    const Value *calledVal = CInst->getCalledValue()->stripPointerCasts();
    static bool warned_inline_assembly = false;

    if (CInst->isInlineAsm()) {
        if (!warned_inline_assembly) {
            llvm::errs() << "WARNING: RD: Inline assembler found\n";
            warned_inline_assembly = true;
        }
        std::vector<FunctionCall> functionCalls;
        RDNode *node = createUndefinedCall(CInst);
        functionCalls.emplace_back(node, node, CallType::PLAIN_CALL);
        return functionCalls;
    }

    std::vector<const Function *> functions;
    const Function *function = dyn_cast<Function>(calledVal);
    if (function != nullptr) {
        functions.push_back(function);
    } else {
        functions = getPointsToFunctions(calledVal);
    }
    return createCallsToFunctions(functions, CInst);
}

std::vector<LLVMRDBuilderDense::FunctionCall>
LLVMRDBuilderDense::createCallsToZeroSizeFunctions(const llvm::Function *function,
                                                 const llvm::CallInst *CInst)
{
    std::vector<FunctionCall> functionCalls;
    if (function->isIntrinsic()) {
        RDNode *node = createIntrinsicCall(CInst);
        functionCalls.emplace_back(node, node, CallType::PLAIN_CALL);
    } else if (function->getName() == "pthread_create") {
        functionCalls = createPthreadCreateCalls(CInst);
    } else if (function->getName() == "pthread_join") {
        functionCalls.push_back(createPthreadJoinCall(CInst));
    } else {
        auto type = _options.getAllocationFunction(function->getName());
        RDNode *node = nullptr;
        if (type != AllocationFunction::NONE) {
            if (type == AllocationFunction::REALLOC)
                node = createRealloc(CInst);
            else
                node = createDynAlloc(CInst, type);
        } else {
            node = createUndefinedCall(CInst);
        }
        functionCalls.emplace_back(node, node, CallType::PLAIN_CALL);
    }
    return functionCalls;
}

std::vector<LLVMRDBuilderDense::FunctionCall>
LLVMRDBuilderDense::createCallsToFunctions(const std::vector<const llvm::Function *> &functions,
                                           const llvm::CallInst *CInst)
{
    using namespace std;
    vector<FunctionCall> callFunctions;

    for(const llvm::Function *function : functions) {
        if (auto model = _options.getFunctionModel(function->getName())) {
            auto node = funcFromModel(model, CInst);
            addNode(CInst, node);
            callFunctions.emplace_back(node, node, CallType::PLAIN_CALL);
        } else if (function->size() == 0) {
            auto zeroSizeCallFunctions = createCallsToZeroSizeFunctions(function, CInst);
            callFunctions.insert(callFunctions.end(),
                                 zeroSizeCallFunctions.begin(),
                                 zeroSizeCallFunctions.end());
        } else if (!llvmutils::callIsCompatible(function, CInst)) {
            RDNode *node = createUndefinedCall(CInst);
            callFunctions.emplace_back(node, node, CallType::PLAIN_CALL);
        } else {
            callFunctions.push_back(createCallToFunction(function));
        }
    }

    if (callFunctions.empty()) {
        RDNode *node = createUndefinedCall(CInst);
        callFunctions.emplace_back(node, node, CallType::PLAIN_CALL);
    }

    return callFunctions;
}

std::vector<LLVMRDBuilderDense::FunctionCall>
LLVMRDBuilderDense::createPthreadCreateCalls(const llvm::CallInst *CInst)
{
    using namespace llvm;
    RDNode *root = nullptr;
    RDNode *ret = nullptr;
    threadCreateCalls.push_back(CInst);

    Value *calledValue = CInst->getArgOperand(2);
    std::vector<const Function *> functions;
    if (isa<Function>(calledValue)) {
        functions.push_back(dyn_cast<Function>(calledValue));
    } else {
        functions = getPointsToFunctions(calledValue);
    }

    std::vector<FunctionCall> functionCalls;

    for (const Function *function : functions) {
        auto it = subgraphs_map.find(function);
        if (it == subgraphs_map.end()) {
            std::tie(root, ret) = buildFunction(*function);
        } else {
            root = it->second.root;
            ret = it->second.ret;
        }
        assert(root && ret && "Incomplete subgraph");
        functionCalls.emplace_back(root, ret, CallType::CREATE_THREAD);
    }

    return functionCalls;
}

LLVMRDBuilderDense::FunctionCall
LLVMRDBuilderDense::createPthreadJoinCall(const llvm::CallInst *CInst)
{
    threadJoinCalls.push_back(CInst);
    RDNode *node = createUndefinedCall(CInst);
    return {node, node, CallType::JOIN_THREAD};
}

ReachingDefinitionsGraph LLVMRDBuilderDense::build()
{
    // get entry function
    llvm::Function *F = M->getFunction(_options.entryFunction);
    if (!F) {
        llvm::errs() << "The function '" << _options.entryFunction << "' was not found in the module\n";
        abort();
    }

    // first we must build globals, because nodes can use them as operands
    std::pair<RDNode *, RDNode *> glob = buildGlobals();

    // now we can build rest of the graph
    RDNode *root, *ret;
    std::tie(root, ret) = buildFunction(*F);
    assert(root && "Do not have a root node of a function");
    assert(ret && "Do not have a ret node of a function");

    // do we have any globals at all? If so, insert them at the begining
    // of the graph
    if (glob.first) {
        assert(glob.second && "Have the start but not the end");

        // this is a sequence of global nodes, make it the root of the graph
        makeEdge(glob.second, root);

        assert(root->successorsNum() > 0);
        root = glob.first;
    }

    ReachingDefinitionsGraph graph;
    graph.setRoot(root);

    matchForksAndJoins();

    return graph;
}

std::pair<RDNode *, RDNode *> LLVMRDBuilderDense::buildGlobals()
{
    RDNode *cur = nullptr, *prev, *first = nullptr;
    for (auto I = M->global_begin(), E = M->global_end(); I != E; ++I) {
        prev = cur;

        // every global node is like memory allocation
        cur = new RDNode(RDNodeType::ALLOC);
        addNode(&*I, cur);

        if (prev)
            makeEdge(prev, cur);
        else
            first = cur;
    }

    assert((!first && !cur) || (first && cur));
    return std::pair<RDNode *, RDNode *>(first, cur);
}

///
// Map pointers of 'val' to def-sites.
// \param where  location in the program, for debugging
// \param size is the number of bytes used from the memory
std::vector<DefSite> LLVMRDBuilderDense::mapPointers(const llvm::Value *where,
                                                     const llvm::Value *val,
                                                     Offset size)
{
    std::vector<DefSite> result;

    auto psn = PTA->getLLVMPointsToChecked(val);
    if (!psn.first) {
        result.push_back(DefSite(UNKNOWN_MEMORY));
#ifndef NDEBUG
        llvm::errs() << "[RD] warning at: " << *where << "\n";
        llvm::errs() << "No points-to set for: " << *val << "\n";
#endif
        // don't have points-to information for used pointer
        return result;
    }

    if (psn.second.empty()) {
#ifndef NDEBUG
        llvm::errs() << "[RD] warning at: " << *where << "\n";
        llvm::errs() << "Empty points-to set for: " << *val << "\n";
#endif
        // this may happen on invalid reads and writes to memory,
        // like when you try for example this:
        //
        //   int p, q;
        //   memcpy(p, q, sizeof p);
        //
        // (there should be &p and &q)
        // NOTE: maybe this is a bit strong to say unknown memory,
        // but better be sound then incorrect
        result.push_back(DefSite(UNKNOWN_MEMORY));
        return result;
    }

    result.reserve(psn.second.size());

    if (psn.second.hasUnknown()) {
        result.push_back(DefSite(UNKNOWN_MEMORY));
    }

    for (const auto& ptr: psn.second) {
        if (llvm::isa<llvm::Function>(ptr.value))
            continue;

        RDNode *ptrNode = getOperand(ptr.value);
        if (!ptrNode) {
            // keeping such set is faster then printing it all to terminal
            // ... and we don't flood the terminal that way
            static std::set<const llvm::Value *> warned;
            if (warned.insert(ptr.value).second) {
                llvm::errs() << "[RD] error for " << *val << "\n";
                llvm::errs() << "[RD] error: Haven't created the node for the pointer to:\n";
                llvm::errs() << *ptr.value << "\n";
            }
            continue;
        }

        // FIXME: we should pass just size to the DefSite ctor, but the old code relies
        // on the behavior that when offset is unknown, the length is also unknown.
        // So for now, mimic the old code. Remove it once we fix the old code.
        result.push_back(DefSite(ptrNode, ptr.offset, ptr.offset.isUnknown() ? Offset::UNKNOWN : size));
    }

    return result;
}

LLVMRDBuilderDense::FunctionCall::FunctionCall(RDNode *rootNode,
                                               RDNode *returnNode,
                                               LLVMRDBuilderDense::CallType callType):rootNode(rootNode),
                                                                                      returnNode(returnNode),
                                                                                      callType(callType) {}

} // namespace rd
} // namespace analysis
} // namespace dg

