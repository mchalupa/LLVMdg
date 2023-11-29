#include <llvm/IR/IntrinsicInst.h>
#include <set>
#include <unordered_map>
#include <utility>

#include <llvm/Config/llvm-config.h>

#if ((LLVM_VERSION_MAJOR == 3) && (LLVM_VERSION_MINOR < 5))
#include <llvm/Support/CFG.h>
#else
#include <llvm/IR/CFG.h>
#endif

#include <llvm/IR/DataLayout.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Value.h>
#include <llvm/Support/raw_ostream.h>

#include "dg/llvm/LLVMDependenceGraph.h"
#include "dg/llvm/LLVMNode.h"
#include "dg/llvm/PointerAnalysis/PointerAnalysis.h"
#include "dg/llvm/ThreadRegions/ControlFlowGraph.h"
#include "dg/llvm/ThreadRegions/MayHappenInParallel.h"

#include "llvm/ControlDependence/InterproceduralCD.h"
#include "llvm/ControlDependence/NTSCD.h"
#include "llvm/ControlDependence/legacy/NTSCD.h"

#include "dg/util/debug.h"
#include "llvm-utils.h"
#include "llvm/LLVMDGVerifier.h"

#include "dg/ADT/Queue.h"

#include "DefUse/DefUse.h"

using llvm::errs;
using std::make_pair;

namespace dg {

/// ------------------------------------------------------------------
//  -- LLVMDependenceGraph
/// ------------------------------------------------------------------

// map of all constructed functions
std::map<llvm::Value *, LLVMDependenceGraph *> constructedFunctions;

const std::map<llvm::Value *, LLVMDependenceGraph *> &
getConstructedFunctions() {
    return constructedFunctions;
}

LLVMDependenceGraph::~LLVMDependenceGraph() {
    // delete nodes
    for (auto &I : *this) {
        LLVMNode *node = I.second;

        if (node) {
            for (LLVMDependenceGraph *subgraph : node->getSubgraphs()) {
                // graphs are referenced, once the refcount is 0
                // the graph will be deleted
                // Because of recursive calls, graph can be its
                // own subgraph. In that case we're in the destructor
                // already, so do not delete it
                subgraph->unref(subgraph != this);
            }

            // delete parameters (on null it is no op)
            delete node->getParameters();

#ifdef DEBUG_ENABLED
            if (!node->getBBlock() && !llvm::isa<llvm::Function>(*I.first))
                llvmutils::printerr("Had no BB assigned", I.first);
#endif

            delete node;
        } else {
#ifdef DEBUG_ENABLED
            llvmutils::printerr("Had no node assigned", I.first);
#endif //
        }
    }

    // delete global nodes if this is the last graph holding them
    if (global_nodes && global_nodes.use_count() == 1) {
        for (auto &it : *global_nodes)
            delete it.second;
    }

    // delete formal parameters
    delete getParameters();

    // delete post-dominator tree root
    delete getPostDominatorTreeRoot();
}

static void addGlobals(llvm::Module *m, LLVMDependenceGraph *dg) {
    DBG_SECTION_BEGIN(llvmdg, "Building globals");
    // create a container for globals,
    // it will be inherited to subgraphs
    dg->allocateGlobalNodes();

    for (auto I = m->global_begin(), E = m->global_end(); I != E; ++I)
        dg->addGlobalNode(new LLVMNode(&*I));
    DBG_SECTION_END(llvmdg, "Done building globals");
}

bool LLVMDependenceGraph::verify() const {
    LLVMDGVerifier verifier(this);
    return verifier.verify();
}

void LLVMDependenceGraph::setThreads(bool threads) { this->threads = threads; }

LLVMNode *LLVMDependenceGraph::findNode(llvm::Value *value) const {
    auto iterator = nodes.find(value);
    if (iterator != nodes.end()) {
        return iterator->second;
    }
    return nullptr;
}

bool LLVMDependenceGraph::build(llvm::Module *m, llvm::Function *entry) {
    DBG_SECTION_BEGIN(llvmdg, "Building dependence graphs for the module");
    // get entry function if not given
    if (entry)
        entryFunction = entry;
    else
        entryFunction = m->getFunction("main");

    if (!entryFunction) {
        errs() << "No entry function found/given\n";
        return false;
    }

    module = m;

    // add global nodes. These will be shared across subgraphs
    addGlobals(m, this);

    // build recursively DG from entry point
    build(entryFunction);

    DBG_SECTION_END(llvmdg, "Done building dependence graphs for the module");
    return true;
};

LLVMDependenceGraph *LLVMDependenceGraph::buildSubgraph(LLVMNode *node) {
    using namespace llvm;

    Value *val = node->getValue();
    CallInst *CInst = dyn_cast<CallInst>(val);
    assert(CInst && "buildSubgraph called on non-CallInst");
    Function *callFunc = CInst->getCalledFunction();

    return buildSubgraph(node, callFunc);
}

// FIXME don't duplicate the code
bool LLVMDependenceGraph::addFormalGlobal(llvm::Value *val) {
    // add the same formal parameters
    LLVMDGParameters *params = getOrCreateParameters();
    assert(params);

    // if we have this value, just return
    if (params->find(val))
        return false;

    LLVMNode *fpin, *fpout;
    std::tie(fpin, fpout) = params->constructGlobal(val, val, this);
    assert(fpin && fpout);
    assert(fpin->getDG() == this && fpout->getDG() == this);

    LLVMNode *entry = getEntry();
    entry->addControlDependence(fpin);
    entry->addControlDependence(fpout);

    // if these are the formal parameters of the main
    // function, add control dependence also between the
    // global as the formal input parameter representing this global
    if (llvm::Function *F = llvm::dyn_cast<llvm::Function>(entry->getValue())) {
        if (F == entryFunction) {
            auto *gnode = getGlobalNode(val);
            assert(gnode);
            gnode->addControlDependence(fpin);
        }
    }

    return true;
}

static bool addSubgraphGlobParams(LLVMDependenceGraph *parentdg,
                                  LLVMDGParameters *params) {
    bool changed = false;
    for (auto it = params->global_begin(), et = params->global_end(); it != et;
         ++it)
        changed |= parentdg->addFormalGlobal(it->first);

    // and add heap-allocated variables
    for (const auto &it : *params) {
        if (llvm::isa<llvm::CallInst>(it.first))
            changed |= parentdg->addFormalParameter(it.first);
    }

    return changed;
}

void LLVMDependenceGraph::addSubgraphGlobalParameters(
        LLVMDependenceGraph *subgraph) {
    LLVMDGParameters *params = subgraph->getParameters();
    if (!params)
        return;

    // if we do not change anything, it means that the graph
    // has these params already, and so must the callers of the graph
    if (!addSubgraphGlobParams(this, params))
        return;

    // recursively add the formal parameters to all callers
    for (LLVMNode *callsite : this->getCallers()) {
        LLVMDependenceGraph *graph = callsite->getDG();
        graph->addSubgraphGlobalParameters(this);

        // update the actual parameters of the call-site
        callsite->addActualParameters(this);
    }
}

LLVMDependenceGraph *
LLVMDependenceGraph::buildSubgraph(LLVMNode *node, llvm::Function *callFunc,
                                   bool fork) {
    using namespace llvm;

    LLVMBBlock *BB;

    // if we don't have this subgraph constructed, construct it
    // else just add call edge
    LLVMDependenceGraph *&subgraph = constructedFunctions[callFunc];
    if (!subgraph) {
        // since we have reference the the pointer in
        // constructedFunctions, we can assing to it
        subgraph = new LLVMDependenceGraph();
        // set global nodes to this one, so that
        // we'll share them
        subgraph->setGlobalNodes(getGlobalNodes());
        subgraph->module = module;
        subgraph->PTA = PTA;
        subgraph->threads = this->threads;
        // make subgraphs gather the call-sites too
        subgraph->gatherCallsites(gather_callsites, gatheredCallsites);

        // make the real work
#ifndef NDEBUG
        bool ret =
#endif
                subgraph->build(callFunc);

#ifndef NDEBUG
        // at least for now use just assert, if we'll
        // have a reason to handle such failures at some
        // point, we can change it
        assert(ret && "Building subgraph failed");
#endif

        // we built the subgraph, so it has refcount = 1,
        // later in the code we call addSubgraph, which
        // increases the refcount to 2, but we need this
        // subgraph to has refcount 1, so unref it
        subgraph->unref(false /* deleteOnZero */);
    }

    BB = node->getBBlock();
    assert(BB && "do not have BB; this is a bug, sir");
    BB->addCallsite(node);

    // add control dependence from call node
    // to entry node
    node->addControlDependence(subgraph->getEntry());

    // add globals that are used in subgraphs
    // it is necessary if this subgraph was creating due to function
    // pointer call
    addSubgraphGlobalParameters(subgraph);
    node->addActualParameters(subgraph, callFunc, fork);

    if (auto *noret = subgraph->getNoReturn()) {
        assert(node->getParameters()); // we created them a while ago
        auto *actnoret = getOrCreateNoReturn(node);
        noret->addControlDependence(actnoret);
    }

    return subgraph;
}

static bool is_func_defined(const llvm::Function *func) {
    return !(!func || func->empty());
}

LLVMNode *LLVMDependenceGraph::getOrCreateNoReturn() {
    // add the same formal parameters
    LLVMDGParameters *params = getOrCreateParameters();
    LLVMNode *noret = params->getNoReturn();
    if (!noret) {
        auto *UI = new llvm::UnreachableInst(getModule()->getContext());
        noret = new LLVMNode(UI, true);
        params->addNoReturn(noret);
        auto *entry = getEntry();
        assert(entry);
        entry->addControlDependence(noret);
    }
    return noret;
}

LLVMNode *LLVMDependenceGraph::getOrCreateNoReturn(LLVMNode *call) {
    LLVMDGParameters *params = call->getOrCreateParameters();
    assert(params);

    LLVMNode *noret = params->getNoReturn();
    if (!noret) {
        auto *UI = new llvm::UnreachableInst(getModule()->getContext());
        noret = new LLVMNode(UI, true);
        params->addNoReturn(noret);
        // this edge is redundant...
        call->addControlDependence(noret);
    }
    return noret;
}

LLVMDGParameters *LLVMDependenceGraph::getOrCreateParameters() {
    LLVMDGParameters *params = getParameters();
    if (!params) {
        params = new LLVMDGParameters();
        setParameters(params);
    }

    return params;
}

bool LLVMDependenceGraph::addFormalParameter(llvm::Value *val) {
    // add the same formal parameters
    LLVMDGParameters *params = getOrCreateParameters();

    // if we have this value, just return
    if (params->find(val))
        return false;

    LLVMNode *fpin, *fpout;
    std::tie(fpin, fpout) = params->construct(val, val, this);
    assert(fpin && fpout);
    assert(fpin->getDG() == this && fpout->getDG() == this);

    LLVMNode *entry = getEntry();
    entry->addControlDependence(fpin);
    entry->addControlDependence(fpout);

    // if these are the formal parameters of the main
    // function and val is a global variable,
    // add control dependence also between the global
    // and the formal input parameter representing this global
    if (llvm::isa<llvm::GlobalVariable>(val)) {
        if (llvm::Function *F =
                    llvm::dyn_cast<llvm::Function>(entry->getValue())) {
            if (F == entryFunction) {
                auto *gnode = getGlobalNode(val);
                assert(gnode);
                gnode->addControlDependence(fpin);
            }
        }
    }

    return true;
}

// FIXME copied from PointsTo.cpp, don't duplicate,
// add it to analysis generic
static bool isMemAllocationFunc(const llvm::Function *func) {
    if (!func || !func->hasName())
        return false;

    const llvm::StringRef &name = func->getName();
    return name.equals("malloc") || name.equals("calloc") ||
           name.equals("realloc");
}

void LLVMDependenceGraph::handleInstruction(llvm::Value *val, LLVMNode *node,
                                            LLVMNode *prevNode) {
    using namespace llvm;

    if (CallInst *CInst = dyn_cast<CallInst>(val)) {
#if LLVM_VERSION_MAJOR >= 8
        Value *strippedValue = CInst->getCalledOperand()->stripPointerCasts();
#else
        Value *strippedValue = CInst->getCalledValue()->stripPointerCasts();
#endif
        Function *func = dyn_cast<Function>(strippedValue);
        // if func is nullptr, then this is indirect call
        // via function pointer. If we have the points-to information,
        // create the subgraph
        if (!func && !CInst->isInlineAsm() && PTA) {
            using namespace dg::pta;
            auto pts = PTA->getLLVMPointsTo(strippedValue);
            if (pts.empty()) {
                llvmutils::printerr("Had no PTA node", strippedValue);
            }
            for (const LLVMPointer &ptr : pts) {
                // vararg may introduce imprecision here, so we
                // must check that it is really pointer to a function
                Function *F = dyn_cast<Function>(ptr.value);
                if (!F)
                    continue;

                if (F->empty() || !llvmutils::callIsCompatible(F, CInst)) {
                    if (threads && F && F->getName() == "pthread_create") {
                        auto possibleFunctions = getCalledFunctions(
                                CInst->getArgOperand(2), PTA);
                        for (auto &function : possibleFunctions) {
                            if (!function->empty()) {
                                LLVMDependenceGraph *subg = buildSubgraph(
                                        node,
                                        const_cast<llvm::Function *>(function),
                                        true /*this is fork*/);
                                node->addSubgraph(subg);
                            }
                        }
                    } else {
                        // incompatible prototypes or the function
                        // is only declaration
                        continue;
                    }
                } else {
                    LLVMDependenceGraph *subg = buildSubgraph(node, F);
                    node->addSubgraph(subg);
                }
            }
        }

        if (func && gather_callsites &&
            func->getName().equals(gather_callsites)) {
            gatheredCallsites->insert(node);
        }

        if (is_func_defined(func)) {
            LLVMDependenceGraph *subg = buildSubgraph(node, func);
            node->addSubgraph(subg);
        }

        // if we allocate a memory in a function, we can pass
        // it to other functions, so it is like global.
        // We need it as parameter, so that if we define it,
        // we can add def-use edges from parent, through the parameter
        // to the definition
        if (isMemAllocationFunc(CInst->getCalledFunction()))
            addFormalParameter(val);

        if (threads && func && func->getName() == "pthread_create") {
            auto possibleFunctions =
                    getCalledFunctions(CInst->getArgOperand(2), PTA);
            for (auto &function : possibleFunctions) {
                auto *subg = buildSubgraph(
                        node, const_cast<llvm::Function *>(function),
                        true /*this is fork*/);
                node->addSubgraph(subg);
            }
        }

        // no matter what is the function, this is a CallInst,
        // so create call-graph
        addCallNode(node);
    } else if (isa<UnreachableInst>(val)) {
        auto *noret = getOrCreateNoReturn();
        node->addControlDependence(noret);
        // unreachable is being inserted because of the previous instr
        // aborts the program. This means that whether it is executed
        // depends on the previous instr
        if (prevNode)
            prevNode->addControlDependence(noret);
    } else if (Instruction *Inst = dyn_cast<Instruction>(val)) {
        if (isa<LoadInst>(val) || isa<GetElementPtrInst>(val)) {
            Value *op = Inst->getOperand(0)->stripInBoundsOffsets();
            if (isa<GlobalVariable>(op))
                addFormalGlobal(op);
        } else if (isa<StoreInst>(val)) {
            Value *op = Inst->getOperand(0)->stripInBoundsOffsets();
            if (isa<GlobalVariable>(op))
                addFormalGlobal(op);

            op = Inst->getOperand(1)->stripInBoundsOffsets();
            if (isa<GlobalVariable>(op))
                addFormalGlobal(op);
        }
    }
}

LLVMBBlock *LLVMDependenceGraph::build(llvm::BasicBlock &llvmBB) {
    DBG(llvmdg, "Building basic block");
    using namespace llvm;

    LLVMBBlock *BB = new LLVMBBlock();
    LLVMNode *node = nullptr;
    LLVMNode *prevNode = nullptr;

    BB->setKey(&llvmBB);

    // iterate over the instruction and create node for every single one of them
    for (Instruction &Inst : llvmBB) {
        prevNode = node;

        Value *val = &Inst;
        node = new LLVMNode(val);

        // add new node to this dependence graph
        addNode(node);

        // add the node to our basic block
        BB->append(node);

        // take instruction specific actions
        handleInstruction(val, node, prevNode);
    }

    // did we created at least one node?
    if (!node) {
        assert(llvmBB.empty());
        return BB;
    }

    // check if this is the exit node of function
    // (node is now the last instruction in this BB)
    // if it is, connect it to one artificial return node
    Value *termval = node->getValue();
    if (isa<ReturnInst>(termval)) {
        // create one unified exit node from function and add control dependence
        // to it from every return instruction. We could use llvm pass that
        // would do it for us, but then we would lost the advantage of working
        // on dep. graph that is not for whole llvm
        LLVMNode *ext = getExit();
        if (!ext) {
            // we need new llvm value, so that the nodes won't collide
            ReturnInst *phonyRet = ReturnInst::Create(termval->getContext());
            if (!phonyRet) {
                errs() << "ERR: Failed creating phony return value "
                       << "for exit node\n";
                // XXX later we could return somehow more mercifully
                abort();
            }

            ext = new LLVMNode(phonyRet, true /* node owns the value -
                                                 it will delete it */);
            setExit(ext);

            LLVMBBlock *retBB = new LLVMBBlock(ext);
            retBB->deleteNodesOnDestruction();
            setExitBB(retBB);
            assert(!unifiedExitBB &&
                   "We should not have it assinged yet (or again) here");
            unifiedExitBB = std::unique_ptr<LLVMBBlock>(retBB);
        }

        // add control dependence from this (return) node to EXIT node
        assert(node && "BUG, no node after we went through basic block");
        node->addControlDependence(ext);
        BB->addSuccessor(getExitBB(), LLVMBBlock::ARTIFICIAL_BBLOCK_LABEL);
    }

    // sanity check if we have the first and the last node set
    assert(BB->getFirstNode() && "No first node in BB");
    assert(BB->getLastNode() && "No last node in BB");

    return BB;
}

static LLVMBBlock *createSingleExitBB(LLVMDependenceGraph *graph) {
    llvm::UnreachableInst *ui =
            new llvm::UnreachableInst(graph->getModule()->getContext());
    LLVMNode *exit = new LLVMNode(ui, true);
    graph->addNode(exit);
    graph->setExit(exit);
    LLVMBBlock *exitBB = new LLVMBBlock(exit);
    graph->setExitBB(exitBB);

    // XXX should we add predecessors? If the function does not
    // return anything, we don't need propagate anything outside...
    return exitBB;
}

static void addControlDepsToPHI(LLVMDependenceGraph *graph, LLVMNode *node,
                                const llvm::PHINode *phi) {
    using namespace llvm;

    const BasicBlock *this_block = phi->getParent();
    auto &CB = graph->getBlocks();

    for (auto I = phi->block_begin(), E = phi->block_end(); I != E; ++I) {
        BasicBlock *B = *I;

        if (B == this_block)
            continue;

        LLVMBBlock *our = CB[B];
        assert(our && "Don't have block constructed for PHI node");
        our->getLastNode()->addControlDependence(node);
    }
}

static void addControlDepsToPHIs(LLVMDependenceGraph *graph) {
    // some phi nodes just work like this
    //
    //  ; <label>:0
    //  %1 = load i32, i32* %a, align 4
    //  %2 = load i32, i32* %b, align 4
    //  %3 = icmp sgt i32 %1, %2
    //  br i1 %3, label %4, label %5
    //
    //  ; <label>:4                                       ; preds = %0
    //  br label %6
    //
    //  ; <label>:5                                       ; preds = %0
    //  br label %6
    //
    //  ; <label>:6                                       ; preds = %5, %4
    //  %p.0 = phi i32* [ %a, %4 ], [ %b, %5 ]
    //
    //  so we need to keep the blocks %5 and %6 even though it is empty

    // add control dependence to each block going to this phi
    // XXX: it is over-approximation, but we don't have nothing better now
    for (auto I = graph->begin(), E = graph->end(); I != E; ++I) {
        llvm::Value *val = I->first;
        if (llvm::PHINode *phi = llvm::dyn_cast<llvm::PHINode>(val)) {
            addControlDepsToPHI(graph, I->second, phi);
        }
    }
}

bool LLVMDependenceGraph::build(llvm::Function *func) {
    using namespace llvm;

    assert(func && "Passed no func");

    DBG_SECTION_BEGIN(llvmdg, "Building function " << func->getName().str());

    // do we have anything to process?
    if (func->empty())
        return false;

    constructedFunctions.insert(make_pair(func, this));

    // create entry node
    LLVMNode *entry = new LLVMNode(func);
    addGlobalNode(entry);
    // we want the entry node to have this DG set
    entry->setDG(this);
    setEntry(entry);

    // add formal parameters to this graph
    addFormalParameters();

    // iterate over basic blocks
    BBlocksMapT &blocks = getBlocks();
    for (llvm::BasicBlock &llvmBB : *func) {
        LLVMBBlock *BB = build(llvmBB);
        blocks[&llvmBB] = BB;

        // first basic block is the entry BB
        if (!getEntryBB())
            setEntryBB(BB);
    }

    assert(blocks.size() == func->size() && "Did not created all blocks");

    DBG(llvmdg, "Adding CFG structure to function " << func->getName().str());
    // add CFG edges
    for (auto &it : blocks) {
        BasicBlock *llvmBB = cast<BasicBlock>(it.first);
        LLVMBBlock *BB = it.second;
        BB->setDG(this);

        int idx = 0;
        for (succ_iterator S = succ_begin(llvmBB), SE = succ_end(llvmBB);
             S != SE; ++S) {
            LLVMBBlock *succ = blocks[*S];
            assert(succ && "Missing basic block");

            // don't let overflow the labels silently
            // if this ever happens, we need to change bit-size
            if (idx >= LLVMBBlock::MAX_BBLOCK_LABEL) {
                errs() << "Too much of successors";
                abort();
            }

            BB->addSuccessor(succ, idx++);
        }
    }

    // if graph has no return inst, just create artificial exit node
    // and point there
    if (!getExit()) {
        assert(!unifiedExitBB && "We should not have exit BB");
        unifiedExitBB = std::unique_ptr<LLVMBBlock>(createSingleExitBB(this));
    }

    // check if we have everything
    assert(getEntry() && "Missing entry node");
    assert(getExit() && "Missing exit node");
    assert(getEntryBB() && "Missing entry BB");
    assert(getExitBB() && "Missing exit BB");

    addControlDepsToPHIs(this);

    // add CFG edge from entry point to the first instruction
    entry->addControlDependence(getEntryBB()->getFirstNode());

    DBG_SECTION_END(llvmdg, "Done building function " << func->getName().str());

    return true;
}

bool LLVMDependenceGraph::build(llvm::Module *m, LLVMPointerAnalysis *pts,
                                LLVMDataDependenceAnalysis *rda,
                                llvm::Function *entry) {
    this->PTA = pts;
    this->DDA = rda;
    return build(m, entry);
}

void LLVMDependenceGraph::addFormalParameters() {
    using namespace llvm;

    LLVMNode *entryNode = getEntry();
    assert(entryNode && "No entry node when adding formal parameters");

    Function *func = dyn_cast<Function>(entryNode->getValue());
    assert(func && "entry node value is not a function");
    // assert(func->arg_size() != 0 && "This function is undefined?");
    if (func->arg_size() == 0)
        return;

    LLVMDGParameters *params = getOrCreateParameters();

    LLVMNode *in, *out;
    for (auto I = func->arg_begin(), E = func->arg_end(); I != E; ++I) {
        Value *val = (&*I);

        std::tie(in, out) = params->construct(val, val, this);
        assert(in && out);

        // add control edges
        entryNode->addControlDependence(in);
        entryNode->addControlDependence(out);
    }

    if (func->isVarArg()) {
        Value *val = ConstantPointerNull::get(func->getType());
        val->setName("vararg");
        in = new LLVMNode(val, true);
        out = new LLVMNode(val, true);
        in->setDG(this);
        out->setDG(this);

        params->setVarArg(in, out);
        entryNode->addControlDependence(in);
        entryNode->addControlDependence(out);
        in->addDataDependence(out);
    }
}

static bool array_match(llvm::StringRef name, const char *names[]) {
    unsigned idx = 0;
    while (names[idx]) {
        if (name.equals(names[idx]))
            return true;
        ++idx;
    }

    return false;
}

static bool array_match(llvm::StringRef name,
                        const std::vector<std::string> &names) {
    for (const auto &nm : names) {
        if (name == nm)
            return true;
    }

    return false;
}

static bool match_callsite_name(LLVMNode *callNode, const char *names[]) {
    using namespace llvm;

    // if the function is undefined, it has no subgraphs,
    // but is not called via function pointer
    if (!callNode->hasSubgraphs()) {
        const CallInst *callInst = cast<CallInst>(callNode->getValue());
#if LLVM_VERSION_MAJOR >= 8
        const Value *calledValue = callInst->getCalledOperand();
#else
        const Value *calledValue = callInst->getCalledValue();
#endif
        const Function *func =
                dyn_cast<Function>(calledValue->stripPointerCasts());
        // in the case we haven't run points-to analysis
        if (!func)
            return false;

        // otherwise we would have a subgraph
        assert(func->size() == 0);
        return array_match(func->getName(), names);
    } // simply iterate over the subgraphs, get the entry node
    // and check it
    for (LLVMDependenceGraph *dg : callNode->getSubgraphs()) {
        LLVMNode *entry = dg->getEntry();
        assert(entry && "No entry node in graph");

        const Function *func =
                cast<Function>(entry->getValue()->stripPointerCasts());
        if (array_match(func->getName(), names)) {
            return true;
        }
    }

    return false;
}

static bool match_callsite_name(LLVMNode *callNode,
                                const std::vector<std::string> &names) {
    using namespace llvm;

    // if the function is undefined, it has no subgraphs,
    // but is not called via function pointer
    if (!callNode->hasSubgraphs()) {
        const CallInst *callInst = cast<CallInst>(callNode->getValue());
#if LLVM_VERSION_MAJOR >= 8
        const Value *calledValue = callInst->getCalledOperand();
#else
        const Value *calledValue = callInst->getCalledValue();
#endif
        const Function *func =
                dyn_cast<Function>(calledValue->stripPointerCasts());
        // in the case we haven't run points-to analysis
        if (!func)
            return false;

        return array_match(func->getName(), names);
    } // simply iterate over the subgraphs, get the entry node
    // and check it
    for (LLVMDependenceGraph *dg : callNode->getSubgraphs()) {
        LLVMNode *entry = dg->getEntry();
        assert(entry && "No entry node in graph");

        const Function *func =
                cast<Function>(entry->getValue()->stripPointerCasts());
        if (array_match(func->getName(), names)) {
            return true;
        }
    }

    return false;
}

bool LLVMDependenceGraph::getCallSites(const char *name,
                                       std::set<LLVMNode *> *callsites) {
    const char *names[] = {name, nullptr};
    return getCallSites(names, callsites);
}

bool LLVMDependenceGraph::getCallSites(const char *names[],
                                       std::set<LLVMNode *> *callsites) {
    for (auto &F : constructedFunctions) {
        for (auto &I : F.second->getBlocks()) {
            LLVMBBlock *BB = I.second;
            for (LLVMNode *n : BB->getNodes()) {
                if (llvm::isa<llvm::CallInst>(n->getValue())) {
                    if (match_callsite_name(n, names))
                        callsites->insert(n);
                }
            }
        }
    }

    return !callsites->empty();
}

bool LLVMDependenceGraph::getCallSites(const std::vector<std::string> &names,
                                       std::set<LLVMNode *> *callsites) {
    for (const auto &F : constructedFunctions) {
        for (const auto &I : F.second->getBlocks()) {
            LLVMBBlock *BB = I.second;
            for (LLVMNode *n : BB->getNodes()) {
                if (llvm::isa<llvm::CallInst>(n->getValue())) {
                    if (match_callsite_name(n, names))
                        callsites->insert(n);
                }
            }
        }
    }

    return !callsites->empty();
}

void LLVMDependenceGraph::computeNTSCD(
        const LLVMControlDependenceAnalysisOptions &opts) {
    DBG_SECTION_BEGIN(llvmdg, "Filling in CDA edges (NTSCD)");
    dg::LLVMControlDependenceAnalysis ntscd(this->module, opts);
    assert(opts.ntscdCD() || opts.ntscd2CD());

    for (const auto &it : getConstructedFunctions()) {
        auto &blocks = it.second->getBlocks();
        for (auto &BB : *llvm::cast<llvm::Function>(it.first)) {
            auto *bb = blocks[&BB];
            assert(bb);
            for (auto *dep : ntscd.getDependencies(&BB)) {
                auto *depbb = blocks[dep];
                assert(depbb);
                depbb->addControlDependence(bb);
            }

            for (auto &I : BB) {
                for (auto *dep : ntscd.getDependencies(&I)) {
                    auto *depnd = it.second->getNode(dep);
                    assert(depnd);
                    auto *ind = it.second->getNode(&I);
                    assert(ind);
                    depnd->addControlDependence(ind);
                }
            }
        }
    }

    DBG_SECTION_END(llvmdg, "Done computing CDA edges");
}

void LLVMDependenceGraph::computeNonTerminationControlDependencies() {
    DBG_SECTION_BEGIN(llvmdg, "Computing NTSCD");
    llvmdg::legacy::NTSCD ntscdAnalysis(this->module, {}, PTA);
    ntscdAnalysis.computeDependencies();
    const auto &dependencies = ntscdAnalysis.controlDependencies();

    for (const auto &dep : dependencies) {
        if (dep.first->isArtificial()) {
            continue;
        }

        auto *lastInstruction = findInstruction(
                castToLLVMInstruction(dep.first->lastInstruction()),
                getConstructedFunctions());
        for (auto *const dependant : dep.second) {
            for (const auto *const instruction :
                 dependant->llvmInstructions()) {
                auto *dgInstruction =
                        findInstruction(castToLLVMInstruction(instruction),
                                        getConstructedFunctions());
                if (lastInstruction && dgInstruction) {
                    lastInstruction->addControlDependence(dgInstruction);
                } else {
                    static std::set<std::pair<LLVMNode *, LLVMNode *>> reported;
                    if (reported.insert({lastInstruction, dgInstruction})
                                .second) {
                        llvm::errs() << "[CD] error: CD could not be set up, "
                                        "some instruction was not found:\n";
                        if (lastInstruction)
                            llvm::errs()
                                    << "[CD] last instruction: "
                                    << *lastInstruction->getValue() << "\n";
                        else
                            llvm::errs() << "[CD] No last instruction\n";
                        if (dgInstruction)
                            llvm::errs() << "[CD] current instruction: "
                                         << *dgInstruction->getValue() << "\n";
                        else
                            llvm::errs() << "[CD] No current instruction\n";
                    }
                }
            }
            if (dependant->isExit() && lastInstruction) {
                auto *dg = lastInstruction->getDG();
                auto *noret = dg->getOrCreateNoReturn();
                lastInstruction->addControlDependence(noret);

                // we added the formal noreturn, now add the noreturn to every
                // callnode
                for (auto *caller : dg->getCallers()) {
                    caller->getOrCreateParameters(); // create params if not
                                                     // created
                    auto *actnoret = dg->getOrCreateNoReturn(caller);
                    noret->addControlDependence(actnoret);
                }
            }
        }
    }
    DBG_SECTION_END(llvmdg, "Done computing NTSCD");
}

void LLVMDependenceGraph::computeInterferenceDependentEdges(
        ControlFlowGraph *controlFlowGraph) {
    auto regions = controlFlowGraph->threadRegions();
    MayHappenInParallel mayHappenInParallel(regions);

    for (const auto &currentRegion : regions) {
        auto llvmValuesForCurrentRegion = currentRegion->llvmInstructions();
        auto currentRegionLoads =
                getLoadInstructions(llvmValuesForCurrentRegion);
        auto currentRegionStores =
                getStoreInstructions(llvmValuesForCurrentRegion);
        auto parallelRegions =
                mayHappenInParallel.parallelRegions(currentRegion);
        for (const auto &parallelRegion : parallelRegions) {
            auto llvmInstructionsForParallelRegion =
                    parallelRegion->llvmInstructions();
            auto parallelRegionLoads =
                    getLoadInstructions(llvmInstructionsForParallelRegion);
            auto parallelRegionStores =
                    getStoreInstructions(llvmInstructionsForParallelRegion);
            computeInterferenceDependentEdges(currentRegionLoads,
                                              parallelRegionStores);
            computeInterferenceDependentEdges(parallelRegionLoads,
                                              currentRegionStores);
        }
    }
}

void LLVMDependenceGraph::computeForkJoinDependencies(
        ControlFlowGraph *controlFlowGraph) {
    auto joins = controlFlowGraph->getJoins();
    for (const auto &join : joins) {
        auto *joinNode = findInstruction(castToLLVMInstruction(join),
                                         constructedFunctions);
        for (const auto &fork : controlFlowGraph->getCorrespondingForks(join)) {
            auto *forkNode = findInstruction(castToLLVMInstruction(fork),
                                             constructedFunctions);
            joinNode->addControlDependence(forkNode);
        }
    }
}

void LLVMDependenceGraph::computeCriticalSections(
        ControlFlowGraph *controlFlowGraph) {
    auto locks = controlFlowGraph->getLocks();
    for (const auto *lock : locks) {
        auto *callLockInst = castToLLVMInstruction(lock);
        auto *lockNode = findInstruction(callLockInst, constructedFunctions);
        auto correspondingNodes =
                controlFlowGraph->getCorrespondingCriticalSection(lock);
        for (const auto *correspondingNode : correspondingNodes) {
            auto *node = castToLLVMInstruction(correspondingNode);
            auto *dependentNode = findInstruction(node, constructedFunctions);
            if (dependentNode) {
                lockNode->addControlDependence(dependentNode);
            } else {
                llvm::errs()
                        << "An instruction " << *node
                        << " was not found, cannot setup"
                        << " control depency on lock " << *callLockInst << "\n";
            }
        }

        auto correspondingUnlocks =
                controlFlowGraph->getCorrespongingUnlocks(lock);
        for (const auto *unlock : correspondingUnlocks) {
            auto *node = castToLLVMInstruction(unlock);
            auto *unlockNode = findInstruction(node, constructedFunctions);
            if (unlockNode) {
                unlockNode->addControlDependence(lockNode);
            }
        }
    }
}

void LLVMDependenceGraph::computeInterferenceDependentEdges(
        const std::set<const llvm::Instruction *> &loads,
        const std::set<const llvm::Instruction *> &stores) {
    for (const auto &load : loads) {
        auto *loadInst = const_cast<llvm::Instruction *>(load);
        auto loadFunction = constructedFunctions.find(
                const_cast<llvm::Function *>(load->getParent()->getParent()));
        if (loadFunction == constructedFunctions.end())
            continue;
        auto *loadNode = loadFunction->second->findNode(loadInst);
        if (!loadNode)
            continue;

        for (const auto &store : stores) {
            auto *storeInst = const_cast<llvm::Instruction *>(store);
            auto storeFunction =
                    constructedFunctions.find(const_cast<llvm::Function *>(
                            store->getParent()->getParent()));
            if (storeFunction == constructedFunctions.end())
                continue;
            auto *storeNode = storeFunction->second->findNode(storeInst);
            if (!storeNode)
                continue;

            auto loadPts = PTA->getLLVMPointsTo(load->getOperand(0));
            auto storePts = PTA->getLLVMPointsTo(store->getOperand(1));
            for (const auto &pointerLoad : loadPts) {
                for (const auto &pointerStore : storePts) {
                    if (pointerLoad.value == pointerStore.value &&
                        (pointerLoad.offset.isUnknown() ||
                         pointerStore.offset.isUnknown() ||
                         pointerLoad.offset == pointerStore.offset)) {
                        storeNode->addInterferenceDependence(loadNode);
                    }
                }
            }

            // handle the unknown pointer
            if (loadPts.hasUnknown() || storePts.hasUnknown())
                storeNode->addInterferenceDependence(loadNode);
        }
    }
}

std::set<const llvm::Instruction *> LLVMDependenceGraph::getLoadInstructions(
        const std::set<const llvm::Instruction *> &llvmInstructions) const {
    return getInstructionsOfType(llvm::Instruction::Load, llvmInstructions);
}

std::set<const llvm::Instruction *> LLVMDependenceGraph::getStoreInstructions(
        const std::set<const llvm::Instruction *> &llvmInstructions) const {
    return getInstructionsOfType(llvm::Instruction::Store, llvmInstructions);
}

std::set<const llvm::Instruction *> LLVMDependenceGraph::getInstructionsOfType(
        const unsigned opCode,
        const std::set<const llvm::Instruction *> &llvmInstructions) {
    std::set<const llvm::Instruction *> instructions;
    for (const auto &llvmValue : llvmInstructions) {
        if (llvm::isa<llvm::Instruction>(llvmValue)) {
            const llvm::Instruction *instruction =
                    static_cast<const llvm::Instruction *>(llvmValue);
            if (instruction->getOpcode() == opCode) {
                instructions.insert(instruction);
            }
        }
    }
    return instructions;
}
void LLVMDependenceGraph::computeControlDependencies(
        const LLVMControlDependenceAnalysisOptions &opts) {
    if (opts.standardCD()) {
        computePostDominators(true);
    } else if (opts.ntscdLegacyCD()) {
        computeNonTerminationControlDependencies();
        // the legacy implementation contains a bug, we workaroudn it by running
        // also the intraprocedural version of new NTSCD
        auto tmpopts = opts;
        tmpopts.interprocedural = false;
        tmpopts.algorithm =
                ControlDependenceAnalysisOptions::CDAlgorithm::NTSCD2;
        computeNTSCD(tmpopts);
    } else if (opts.ntscdCD() || opts.ntscd2CD() || opts.ntscdRanganathCD()) {
        computeNTSCD(opts);
    } else
        abort();

    if (opts.interproceduralCD())
        addNoreturnDependencies(opts);
}

void LLVMDependenceGraph::addNoreturnDependencies(LLVMNode *noret,
                                                  LLVMBBlock *from) {
    std::set<LLVMBBlock *> visited;
    ADT::QueueLIFO<LLVMBBlock *> queue;

    for (const auto &succ : from->successors()) {
        if (visited.insert(succ.target).second)
            queue.push(succ.target);
    }

    while (!queue.empty()) {
        auto *cur = queue.pop();

        // do the stuff
        for (auto *node : cur->getNodes())
            noret->addControlDependence(node);

        // queue successors
        for (const auto &succ : cur->successors()) {
            if (visited.insert(succ.target).second)
                queue.push(succ.target);
        }
    }
}

void LLVMDependenceGraph::addNoreturnDependencies(
        const LLVMControlDependenceAnalysisOptions &opts) {
    if (opts.ntscdCD() || opts.ntscd2CD() || opts.ntscdLegacyCD()) {
        llvmdg::LLVMInterprocCD interprocCD(this->module);
        for (const auto &F : getConstructedFunctions()) {
            auto *dg = F.second;
            auto *fun = llvm::cast<llvm::Function>(F.first);
            for (auto *noreti : interprocCD.getNoReturns(fun)) {
                // create noret params if not yet
                auto *fnoret = dg->getOrCreateNoReturn();
                for (auto *caller : dg->getCallers()) {
                    caller->getOrCreateParameters(); // create params if not
                                                     // created
                    auto *actnoret = dg->getOrCreateNoReturn(caller);
                    fnoret->addControlDependence(actnoret);
                }

                // add edge from function's noret to instruction's nodes
                auto *nd = dg->getNode(noreti);
                assert(nd);
                // if this is a call, add the dependence to noret param
                if (llvm::isa<llvm::CallInst>(nd->getValue())) {
                    nd = getOrCreateNoReturn(nd);
                }
                nd->addControlDependence(fnoret);
            }
        }
    }

    // in theory, we should not need this one, but it does not work right now
    for (const auto &F : getConstructedFunctions()) {
        auto &blocks = F.second->getBlocks();

        for (auto &it : blocks) {
            LLVMBBlock *B = it.second;
            std::set<LLVMNode *> noreturns;
            for (auto *node : B->getNodes()) {
                // add dependencies for the found no returns
                for (auto *nrt : noreturns) {
                    nrt->addControlDependence(node);
                }

                // is this a call with a noreturn parameter?
                if (auto *params = node->getParameters()) {
                    if (auto *noret = params->getNoReturn()) {
                        // process the rest of the block
                        noreturns.insert(noret);

                        // process reachable nodes
                        addNoreturnDependencies(noret, B);
                    }
                }
            }
        }
    }
}

void LLVMDependenceGraph::addDefUseEdges(bool preserveDbg) {
    LLVMDefUseAnalysis DUA(this, DDA, PTA);
    DUA.run();

    if (preserveDbg) {
        using namespace llvm;

        for (const auto &it : getConstructedFunctions()) {
            LLVMDependenceGraph *dg = it.second;
            for (auto &I : instructions(cast<Function>(it.first))) {
                Value *val = nullptr;
                if (auto *DI = dyn_cast<DbgDeclareInst>(&I))
                    val = DI->getAddress();
                else if (auto *DI = dyn_cast<DbgValueInst>(&I))
                    val = DI->getValue();
#if LLVM_VERSION_MAJOR > 5
                else if (auto *DI = dyn_cast<DbgAssignIntrinsic>(&I))
                    val = DI->getAddress();
#endif

                if (val) {
                    auto *nd = dg->getNode(&I);
                    auto *ndop = dg->getNode(val);
                    assert(nd && "Do not have a node for a dbg intrinsic");
                    assert(ndop && "Do not have a node for an operand of a dbg "
                                   "intrinsic");
                    // add a use edge such that we preserve
                    // the debugging intrinsic when we preserve
                    // the value it is talking about
                    nd->addUseDependence(ndop);
                }
            }
        }
    }
}

LLVMNode *findInstruction(llvm::Instruction *instruction,
                          const std::map<llvm::Value *, LLVMDependenceGraph *>
                                  &constructedFunctions) {
    auto valueKey =
            constructedFunctions.find(instruction->getParent()->getParent());
    if (valueKey != constructedFunctions.end()) {
        return valueKey->second->findNode(instruction);
    }
    return nullptr;
}

llvm::Instruction *castToLLVMInstruction(const llvm::Value *value) {
    return const_cast<llvm::Instruction *>(
            static_cast<const llvm::Instruction *>(value));
}

} // namespace dg
