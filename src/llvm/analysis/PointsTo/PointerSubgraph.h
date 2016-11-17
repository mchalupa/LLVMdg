#ifndef _LLVM_DG_POINTER_SUBGRAPH_H_
#define _LLVM_DG_POINTER_SUBGRAPH_H_

#include <unordered_map>

#include <llvm/Support/raw_os_ostream.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/Constants.h>

#include "analysis/PointsTo/PointerSubgraph.h"
#include "analysis/PointsTo/Pointer.h"

namespace dg {
namespace analysis {
namespace pta {

typedef std::pair<PSNode *, PSNode *> PSNodesSeq;

class LLVMPointerSubgraphBuilder
{
    const llvm::Module *M;
    const llvm::DataLayout *DL;
    uint64_t field_sensitivity;

    // build pointer state subgraph for given graph
    // \return   root node of the graph
    PSNode *buildFunction(const llvm::Function& F);
    PSNodesSeq buildInstruction(const llvm::Instruction&);
    PSNode *buildNode(const llvm::Value *val);

    void buildPointerSubgraphBlock(const llvm::BasicBlock& block);

    PSNodesSeq buildArguments(const llvm::Function& F);
    PSNodesSeq buildGlobals();

    void transitivelyBuildUses(const llvm::Value *val);

    struct Subgraph {
        Subgraph(PSNode *r1, PSNode *r2, PSNode *va = nullptr)
            : root(r1), ret(r2), vararg(va) {}
        Subgraph(): root(nullptr), ret(nullptr), vararg(nullptr) {}

        // first and last nodes of the subgraph
        PSNode *root;
        PSNode *ret;

        // this is the node where we gather the variadic-length arguments
        PSNode *vararg;
    };

    // add edges that are derived from CFG to the subgraph
    void addProgramStructure();
    void addProgramStructure(const llvm::Function *F, Subgraph& subg);
    PSNodesSeq buildBlockStructure(const llvm::BasicBlock& block);
    void blockAddCalls(const llvm::BasicBlock& block);

    // map of all nodes we created - use to look up operands
    std::unordered_map<const llvm::Value *, PSNodesSeq > nodes_map;
    // map of all built subgraphs - the value type is a pair (root, return)
    std::unordered_map<const llvm::Function *, Subgraph> subgraphs_map;

    // here we'll keep first and last nodes of every built block and
    // connected together according to successors
    std::map<const llvm::BasicBlock *, PSNodesSeq> built_blocks;
    // helper nodes, here we store them to delete the memory later
    std::vector<PSNode *> dummy_nodes;

public:
    // \param field_sensitivity -- how much should be the PS field sensitive:
    //        UNKNOWN_OFFSET means full field sensitivity, 0 means field insensivity
    //        (every pointer with offset greater than 0 will have UNKNOWN_OFFSET)
    LLVMPointerSubgraphBuilder(const llvm::Module *m,
                               uint64_t field_sensitivity = UNKNOWN_OFFSET)
        : M(m), DL(new llvm::DataLayout(m)), field_sensitivity(field_sensitivity)
        {}

    ~LLVMPointerSubgraphBuilder();

    PSNode *buildLLVMPointerSubgraph();

    // create subgraph of function @F (the nodes)
    // and call+return nodes to/from it. This function
    // won't add the CFG edges if not @with_structure
    PSNodesSeq
    createCallToFunction(const llvm::Function *F);

    PSNodesSeq
    createFuncptrCall(const llvm::CallInst *CInst,
                      const llvm::Function *F);


    // let the user get the nodes map, so that we can
    // map the points-to informatio back to LLVM nodes
    const std::unordered_map<const llvm::Value *, PSNodesSeq>&
                                getNodesMap() const { return nodes_map; }

    PSNode *getNode(const llvm::Value *val)
    {
        auto it = nodes_map.find(val);
        if (it == nodes_map.end())
            return nullptr;

        // the node corresponding to the real llvm value
        // is always the last
        //
        // XXX: this holds everywhere except for va_start
        // sequence. Maybe we should use a new class
        // instead of std::pair to represent the sequence
        return it->second.second;
    }

    // this is the same as the getNode, but it
    // creates ConstantExpr
    PSNode *getPointsTo(const llvm::Value *val)
    {
        PSNode *n = getNode(val);
        if (!n)
            n = getConstant(val);

        // if this is a call that returns a pointer,
        // then the points-to is in CALL_RETURN node
        if (n && (n->getType() == pta::CALL
            || n->getType() == pta::CALL_FUNCPTR))
            n = n->getPairedNode();

        return n;
    }

private:
    void addNode(const llvm::Value *val, PSNode *node)
    {
        nodes_map[val] = std::make_pair(node, node);
        node->setUserData(const_cast<llvm::Value *>(val));
    }

    void addNode(const llvm::Value *val, PSNodesSeq seq)
    {
        nodes_map[val] = seq;
        seq.second->setUserData(const_cast<llvm::Value *>(val));
    }

    bool typeCanBePointer(llvm::Type *Ty) const;
    bool isRelevantInstruction(const llvm::Instruction& Inst);

    PSNode *createAlloc(const llvm::Instruction *Inst);
    PSNode *createStore(const llvm::Instruction *Inst);
    PSNode *createLoad(const llvm::Instruction *Inst);
    PSNode *createGEP(const llvm::Instruction *Inst);
    PSNode *createSelect(const llvm::Instruction *Inst);
    PSNode *createPHI(const llvm::Instruction *Inst);
    PSNode *createCast(const llvm::Instruction *Inst);
    PSNode *createReturn(const llvm::Instruction *Inst);
    PSNode *createPtrToInt(const llvm::Instruction *Inst);
    PSNode *createIntToPtr(const llvm::Instruction *Inst);
    PSNode *createAsm(const llvm::Instruction *Inst);

    PSNode *createIrrelevantInst(const llvm::Value *,
                                  bool build_uses = false);
    PSNode *createArgument(const llvm::Argument *);
    void createIrrelevantUses(const llvm::Value *val);

    PSNode *createAdd(const llvm::Instruction *Inst);
    PSNode *createArithmetic(const llvm::Instruction *Inst);
    PSNode *createUnknown(const llvm::Value *val);

    PSNode *getOperand(const llvm::Value *val);
    PSNode *tryGetOperand(const llvm::Value *val);
    PSNode *getConstant(const llvm::Value *val);
    PSNode *createConstantExpr(const llvm::ConstantExpr *CE);
    Pointer handleConstantGep(const llvm::GetElementPtrInst *GEP);
    Pointer handleConstantBitCast(const llvm::BitCastInst *BC);
    Pointer handleConstantPtrToInt(const llvm::PtrToIntInst *P2I);
    Pointer handleConstantIntToPtr(const llvm::IntToPtrInst *I2P);
    Pointer handleConstantAdd(const llvm::Instruction *Inst);
    Pointer handleConstantArithmetic(const llvm::Instruction *Inst);
    Pointer getConstantExprPointer(const llvm::ConstantExpr *CE);

    void checkMemSet(const llvm::Instruction *Inst);
    void addPHIOperands(PSNode *node, const llvm::PHINode *PHI);
    void addPHIOperands(const llvm::Function& F);
    void addArgumentOperands(const llvm::Function *F, PSNode *arg, int idx);
    void addArgumentOperands(const llvm::CallInst *CI, PSNode *arg, int idx);
    void addArgumentsOperands(const llvm::Function *F,
                              const llvm::CallInst *CI = nullptr);
    void addVariadicArgumentOperands(const llvm::Function *F, PSNode *arg);
    void addVariadicArgumentOperands(const llvm::Function *F,
                                     const llvm::CallInst *CI,
                                     PSNode *arg);

    void addReturnNodeOperands(const llvm::Function *F,
                               PSNode *ret,
                               const llvm::CallInst *CI = nullptr);

    void addReturnNodeOperand(const llvm::CallInst *CI, PSNode *op);
    void addReturnNodeOperand(const llvm::Function *F, PSNode *op);
    void addInterproceduralOperands(const llvm::Function *F,
                                    Subgraph& subg,
                                    const llvm::CallInst *CI = nullptr);

    PSNodesSeq createExtract(const llvm::Instruction *Inst);
    PSNodesSeq createCall(const llvm::Instruction *Inst);
    PSNodesSeq createOrGetSubgraph(const llvm::CallInst *,
                                   const llvm::Function *);


    PSNode *handleGlobalVariableInitializer(const llvm::Constant *C,
                                             PSNode *node);
    PSNode *createMemTransfer(const llvm::IntrinsicInst *Inst);

    PSNodesSeq createMemSet(const llvm::Instruction *);
    PSNodesSeq createDynamicMemAlloc(const llvm::CallInst *CInst, int type);
    PSNodesSeq createRealloc(const llvm::CallInst *CInst);
    PSNodesSeq createUnknownCall(const llvm::CallInst *CInst);
    PSNodesSeq createIntrinsic(const llvm::Instruction *Inst);
    PSNodesSeq createVarArg(const llvm::IntrinsicInst *Inst);
};

} // namespace pta
} // namespace dg
} // namespace analysis

#endif
