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
#if (LLVM_VERSION_MINOR < 5)
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


#include "analysis/PointsTo/PointerSubgraph.h"
#include "llvm/analysis/PointsTo/PointerSubgraph.h"
#include "llvm/llvm-utils.h"
#include "ReachingDefinitions.h"

namespace dg {
namespace analysis {
namespace rd {

#if 0
#include <iostream>
#include <sstream>
#include <fstream>
#include <string>

static std::string
getInstName(const llvm::Value *val)
{
    std::ostringstream ostr;
    llvm::raw_os_ostream ro(ostr);

    assert(val);
    ro << *val;
    ro.flush();

    // break the string if it is too long
    return ostr.str();
}

const char *__get_name(const llvm::Value *val, const char *prefix)
{
    static std::string buf;
    buf.reserve(255);
    buf.clear();

    std::string nm = getInstName(val);
    if (prefix)
        buf.append(prefix);

    buf.append(nm);

    return buf.c_str();
}

{
    const char *name = __get_name(val, prefix);
}

{
    if (prefix) {
        std::string nm;
        nm.append(prefix);
        nm.append(name);
    } else
}
#endif

static uint64_t getAllocatedSize(llvm::Type *Ty, const llvm::DataLayout *DL)
{
    // Type can be i8 *null or similar
    if (!Ty->isSized())
            return 0;

    return DL->getTypeAllocSize(Ty);
}

// FIXME: don't duplicate the code (with PSS.cpp)
static uint64_t getDynamicMemorySize(const llvm::Value *op)
{
    using namespace llvm;

    uint64_t size = 0;
    if (const ConstantInt *C = dyn_cast<ConstantInt>(op)) {
        size = C->getLimitedValue();
        // if the size cannot be expressed as an uint64_t,
        // just set it to 0 (that means unknown)
        if (size == ~((uint64_t) 0))
            size = 0;
    }

    return size;
}

enum MemAllocationFuncs {
    NONEMEM = 0,
    MALLOC,
    CALLOC,
    ALLOCA,
    REALLOC,
};

static int getMemAllocationFunc(const llvm::Function *func)
{
    if (!func || !func->hasName())
        return NONEMEM;

    const char *name = func->getName().data();
    if (strcmp(name, "malloc") == 0)
        return MALLOC;
    else if (strcmp(name, "calloc") == 0)
        return CALLOC;
    else if (strcmp(name, "alloca") == 0)
        return ALLOCA;
    else if (strcmp(name, "realloc") == 0)
        return REALLOC;

    return NONEMEM;
}


LLVMRDBuilder::~LLVMRDBuilder() {
    // delete data layout
    delete DL;

    // delete artificial nodes from subgraphs
    for (auto& it : subgraphs_map) {
        assert((it.second.root && it.second.ret) ||
               (!it.second.root && !it.second.ret));
        delete it.second.root;
        delete it.second.ret;
    }

    // delete nodes
    for (auto& it : nodes_map) {
        assert(it.first && "Have a nullptr node mapping");
        delete it.second;
    }

    // delete dummy nodes
    for (RDNode *nd : dummy_nodes)
        delete nd;
}

RDNode *LLVMRDBuilder::createAlloc(const llvm::Instruction *Inst, bool is_heap)
{
    RDNodeType type = is_heap ? DYN_ALLOC : ALLOC;
    RDNode *node = new RDNode(type);
    addNode(Inst, node);

    return node;
}

RDNode *LLVMRDBuilder::createRealloc(const llvm::Instruction *Inst)
{
    RDNode *node = new RDNode(ALLOC);
    addNode(Inst, node);

    uint64_t size = getDynamicMemorySize(Inst->getOperand(1));
    if (size == 0)
        size = UNKNOWN_OFFSET;

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
#if (LLVM_VERSION_MINOR < 5)
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

RDNode *LLVMRDBuilder::createReturn(const llvm::Instruction *Inst)
{
    RDNode *node = new RDNode(RETURN);
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
        node->addOverwrites(ptrNode, 0, UNKNOWN_OFFSET);
    }

    return node;
}

RDNode *LLVMRDBuilder::getOperand(const llvm::Value *val)
{
    RDNode *op = nodes_map[val];
    if (!op)
        return createNode(*llvm::cast<llvm::Instruction>(val));

    return op;
}

RDNode *LLVMRDBuilder::createNode(const llvm::Instruction &Inst)
{
    using namespace llvm;

    RDNode *node = nullptr;
    switch(Inst.getOpcode()) {
        case Instruction::Alloca:
            // we need alloca's as target to DefSites
            node = createAlloc(&Inst);
            break;
        case Instruction::Call:
            node = createCall(&Inst).second;
            break;
        default:
            llvm::errs() << "BUG: " << Inst << "\n";
            abort();
    }

    return node;
}

RDNode *LLVMRDBuilder::createStore(const llvm::Instruction *Inst)
{
    RDNode *node = new RDNode(STORE);
    addNode(Inst, node);

    pta::PSNode *pts = PTA->getPointsTo(Inst->getOperand(1));
    assert(pts && "Don't have the points-to information for store");

    if (pts->pointsTo.empty()) {
        //llvm::errs() << "ERROR: empty STORE points-to: " << *Inst << "\n";

        // this may happen on invalid reads and writes to memory,
        // like when you try for example this:
        //
        //   int p, q;
        //   memcpy(p, q, sizeof p);
        //
        // (there should be &p and &q)
        // NOTE: maybe this is a bit strong to say unknown memory,
        // but better be sound then incorrect
        node->addDef(UNKNOWN_MEMORY);
        return node;
    }

    for (const pta::Pointer& ptr: pts->pointsTo) {
        // XXX we should at least warn?
        if (ptr.isNull())
            continue;

        if (ptr.isUnknown()) {
            node->addDef(UNKNOWN_MEMORY);
            continue;
        }

        const llvm::Value *ptrVal = ptr.target->getUserData<llvm::Value>();
        // this may emerge with vararg function
        if (llvm::isa<llvm::Function>(ptrVal))
            continue;

        RDNode *ptrNode = getOperand(ptrVal);
        //assert(ptrNode && "Don't have created node for pointer's target");
        if (!ptrNode) {
            // keeping such set is faster then printing it all to terminal
            // ... and we don't flood the terminal that way
            static std::set<const llvm::Value *> warned;
            if (warned.insert(ptrVal).second) {
                llvm::errs() << *ptrVal << "\n";
                llvm::errs() << "Don't have created node for pointer's target\n";
            }

            continue;
        }

        uint64_t size;
        if (ptr.offset.isUnknown()) {
            size = UNKNOWN_OFFSET;
        } else {
            size = getAllocatedSize(Inst->getOperand(0)->getType(), DL);
            if (size == 0)
                size = UNKNOWN_OFFSET;
        }

        //llvm::errs() << *Inst << " DEFS >> " << ptr.target->getName() << " ["
        //             << *ptr.offset << " - " << *ptr.offset + size - 1 << "\n";

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
        bool strong_update = pts->pointsTo.size() == 1 && !pts->isHeap();
        node->addDef(ptrNode, ptr.offset, size, strong_update);
    }

    assert(node);
    return node;
}

static bool isRelevantCall(const llvm::Instruction *Inst)
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
        if (getMemAllocationFunc(func))
            // we need memory allocations
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

// return first and last nodes of the block
std::pair<RDNode *, RDNode *>
LLVMRDBuilder::buildBlock(const llvm::BasicBlock& block)
{
    using namespace llvm;

    RDNode *last_node = nullptr;
    // the first node is dummy and serves as a phi from previous
    // blocks so that we can have proper mapping
    RDNode *node = new RDNode(PHI);
    dummy_nodes.push_back(node);
    std::pair<RDNode *, RDNode *> ret(node, nullptr);

    for (const Instruction& Inst : block) {
        // some nodes may have nullptr as mapping,
        // that means that there are no reaching definitions
        // (well, no nodes to be precise) to map that on
        if (node)
            last_node = node;

        assert(last_node != nullptr && "BUG: Last node is null");
        mapping[&Inst] = last_node;

        auto it = nodes_map.find(&Inst);
        if (it != nodes_map.end()) {
            // reuse node if we already created it as an argument
            node = it->second;
        } else {
            switch(Inst.getOpcode()) {
                case Instruction::Alloca:
                    // we need alloca's as target to DefSites
                    node = createAlloc(&Inst);
                    break;
                case Instruction::Store:
                    node = createStore(&Inst);
                    break;
                case Instruction::Ret:
                    // we need create returns, since
                    // these modify CFG and thus data-flow
                    // FIXME: add new type of node NOOP,
                    // and optimize it away later
                    node = createReturn(&Inst);
                    break;
                case Instruction::Call:
                    if (!isRelevantCall(&Inst))
                        break;

                    std::pair<RDNode *, RDNode *> subg = createCall(&Inst);
                    last_node->addSuccessor(subg.first);

                    // new nodes will connect to the return node
                    node = last_node = subg.second;
                    break;
            }
        }

        // if we created a new node, add successor
        if (last_node != node)
            last_node->addSuccessor(node);
    }

    // last node
    ret.second = node;

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
            ptan.second->addSuccessor(succ.first);
            ++num;
        }
    }

    return num;
}

std::pair<RDNode *, RDNode *>
LLVMRDBuilder::createCallToFunction(const llvm::Function *F)
{
    RDNode *callNode, *returnNode;

    // dummy nodes for easy generation
    callNode = new RDNode(CALL);
    returnNode = new RDNode(CALL_RETURN);

    // do not leak the memory of returnNode (the callNode
    // will be added to nodes_map)
    dummy_nodes.push_back(returnNode);

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
    callNode->addSuccessor(root);
    ret->addSuccessor(returnNode);

    return std::make_pair(callNode, returnNode);
}

std::pair<RDNode *, RDNode *>
LLVMRDBuilder::buildFunction(const llvm::Function& F)
{
    // here we'll keep first and last nodes of every built block and
    // connected together according to successors
    std::map<const llvm::BasicBlock *, std::pair<RDNode *, RDNode *>> built_blocks;

    // create root and (unified) return nodes of this subgraph. These are
    // just for our convenience when building the graph, they can be
    // optimized away later since they are noops
    RDNode *root = new RDNode(NOOP);
    RDNode *ret = new RDNode(NOOP);

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
    root->addSuccessor(first);

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
        if (succ_num == 0 && ptan.second->getType() == RETURN)
            rets.push_back(ptan.second);
    }

    // add successors edges from every real return to our artificial ret node
    for (RDNode *r : rets)
        r->addSuccessor(ret);

    return {root, ret};
}

RDNode *LLVMRDBuilder::createUndefinedCall(const llvm::CallInst *CInst)
{
    using namespace llvm;

    RDNode *node = new RDNode(CALL);
    addNode(CInst, node);

    // every pointer we pass into the undefined call may be defined
    // in the function
    for (unsigned int i = 0; i < CInst->getNumArgOperands(); ++i) {
        const Value *llvmOp = CInst->getArgOperand(i);

        // constants cannot be redefined
        if (isa<Constant>(llvmOp))
            continue;

        pta::PSNode *pts = PTA->getPointsTo(llvmOp);
        // if we do not have a pts, this is not pointer
        // relevant instruction. We must do it this way
        // instead of type checking, due to the inttoptr.
        if (!pts)
            continue;

        for (const pta::Pointer& ptr : pts->pointsTo) {
            if (!ptr.isValid())
                continue;

            const llvm::Value *ptrVal = ptr.target->getUserData<llvm::Value>();
            if (llvm::isa<llvm::Function>(ptrVal))
                // function may not be redefined
                continue;

            RDNode *target = getOperand(ptrVal);
            assert(target && "Don't have pointer target for call argument");

            // this call may define this memory
            node->addDef(target, UNKNOWN_OFFSET, UNKNOWN_OFFSET);
        }
    }

    return node;
}

RDNode *LLVMRDBuilder::createIntrinsicCall(const llvm::CallInst *CInst)
{
    using namespace llvm;

    const IntrinsicInst *I = cast<IntrinsicInst>(CInst);
    const Value *dest;
    const Value *lenVal;

    RDNode *ret = new RDNode(CALL);
    addNode(CInst, ret);

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
            ret->addDef(ret, 0, UNKNOWN_OFFSET);
            return ret;
        default:
            return createUndefinedCall(CInst);
    }

    pta::PSNode *pts = PTA->getPointsTo(dest);
    assert(pts && "No points-to information");

    uint64_t len = UNKNOWN_OFFSET;
    if (const ConstantInt *C = dyn_cast<ConstantInt>(lenVal))
        len = C->getLimitedValue();

    for (const pta::Pointer& ptr : pts->pointsTo) {
        if (!ptr.isValid())
            continue;

        const llvm::Value *ptrVal = ptr.target->getUserData<llvm::Value>();
        if (llvm::isa<llvm::Function>(ptrVal))
            continue;

        uint64_t from, to;
        if (ptr.offset.isUnknown()) {
            // if the offset is UNKNOWN, use whole memory
            from = UNKNOWN_OFFSET;
            len = UNKNOWN_OFFSET;
        } else {
            from = *ptr.offset;
        }

        // do not allow overflow
        if (UNKNOWN_OFFSET - from > len)
            to = from + len;
        else
            to = UNKNOWN_OFFSET;

        RDNode *target = getOperand(ptrVal);
        assert(target && "Don't have pointer target for intrinsic call");

        // add the definition
        ret->addDef(target, from, to, true /* strong update */);
    }

    return ret;
}

std::pair<RDNode *, RDNode *>
LLVMRDBuilder::createCall(const llvm::Instruction *Inst)
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

        RDNode *n = createUndefinedCall(CInst);
        return std::make_pair(n, n);
    }

    const Function *func = dyn_cast<Function>(calledVal);
    if (func) {
        if (func->size() == 0) {
            RDNode *n;
            if (func->isIntrinsic()) {
                n = createIntrinsicCall(CInst);
            } else if (int type = getMemAllocationFunc(func)) {
                if (type == REALLOC)
                    n = createRealloc(CInst);
                else
                    n = createAlloc(CInst, true /* heap */);
            } else {
                n = createUndefinedCall(CInst);
            }

            return std::make_pair(n, n);
        } else {
            std::pair<RDNode *, RDNode *> cf
                = createCallToFunction(func);
            addNode(CInst, cf.first);
            return cf;
        }
    } else {
        // function pointer call
        pta::PSNode *op = PTA->getPointsTo(calledVal);
        assert(op && "Don't have points-to information");
        //assert(!op->pointsTo.empty() && "Don't have pointer to the func");
        if (op->pointsTo.empty()) {
            llvm::errs() << "WARNING: a call via a function pointer, but the points-to is empty\n"
                         << *CInst << "\n";
            RDNode *n = createUndefinedCall(CInst);
            return std::make_pair(n, n);
        }

        RDNode *call_funcptr = nullptr, *ret_call = nullptr;

        if (op->pointsTo.size() > 1) {
            for (const pta::Pointer& ptr : op->pointsTo) {
                if (!ptr.isValid())
                    continue;

                // check if it is a function (varargs may
                // introduce some unprecision to func. pointers)
                if (!isa<Function>(ptr.target->getUserData<Value>()))
                    continue;

                const Function *F = ptr.target->getUserData<Function>();
                if (F->size() == 0) {
                    // the function is a declaration only,
                    // there's nothing better we can do
                    RDNode *n = createUndefinedCall(CInst);
                    return std::make_pair(n, n);
                }

                // FIXME: these checks are repeated here, in PSSBuilder
                // and in LLVMDependenceGraph, we should factor them
                // out into a function...
                if (!llvmutils::callIsCompatible(F, CInst))
                    continue;

                std::pair<RDNode *, RDNode *> cf
                    = createCallToFunction(F);

                // connect the graphs
                if (!call_funcptr) {
                    assert(!ret_call);

                    // create the new nodes lazily
                    call_funcptr = new RDNode(CALL);
                    ret_call = new RDNode(CALL_RETURN);
                    addNode(CInst, call_funcptr);
                }

                call_funcptr->addSuccessor(cf.first);
                cf.second->addSuccessor(ret_call);
            }
        } else {
            // don't add redundant nodes if not needed
            const pta::Pointer& ptr = *(op->pointsTo.begin());
            if (ptr.isValid()) {
                const llvm::Value *valF = ptr.target->getUserData<llvm::Value>();
                const llvm::Function *F = llvm::cast<llvm::Function>(valF);

                if (F->size() == 0) {
                    RDNode *n = createUndefinedCall(CInst);
                    return std::make_pair(n, n);
                } else if (llvmutils::callIsCompatible(F, CInst)) {
                    std::pair<RDNode *, RDNode *> cf = createCallToFunction(F);
                    call_funcptr = cf.first;
                    ret_call = cf.second;
                }
            }
        }

        if (!ret_call) {
            assert(!call_funcptr);
            llvm::errs() << "Function pointer call with no compatible pointer: "
                         << *CInst << "\n";

            RDNode *n = createUndefinedCall(CInst);
            return std::make_pair(n, n);
        }

        assert(call_funcptr && ret_call);
        return std::make_pair(call_funcptr, ret_call);
    }
}

RDNode *LLVMRDBuilder::build()
{
    // get entry function
    llvm::Function *F = M->getFunction("main");
    if (!F) {
        llvm::errs() << "Need main function in module\n";
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
        glob.second->addSuccessor(root);

        assert(root->successorsNum() > 0);
        root = glob.first;
    }

    return root;
}

std::pair<RDNode *, RDNode *> LLVMRDBuilder::buildGlobals()
{
    RDNode *cur = nullptr, *prev, *first = nullptr;
    for (auto I = M->global_begin(), E = M->global_end(); I != E; ++I) {
        prev = cur;

        // every global node is like memory allocation
        cur = new RDNode(ALLOC);
        addNode(&*I, cur);

        if (prev)
            prev->addSuccessor(cur);
        else
            first = cur;
    }

    assert((!first && !cur) || (first && cur));
    return std::pair<RDNode *, RDNode *>(first, cur);
}

} // namespace rd
} // namespace analysis
} // namespace dg
