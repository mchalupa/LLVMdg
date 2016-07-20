

#include "DG2Dot.h"
#include "llvm/LLVMNode.h"

using namespace dg;

static std::ostream& operator<<(std::ostream& os, const analysis::Offset& off)
{
    if (off.offset == UNKNOWN_OFFSET)
        os << "UNKNOWN";
    else
        os << off.offset;

    return os;
}

static std::ostream& printLLVMVal(std::ostream& os, const llvm::Value *val)
{
    if (!val) {
        os << "(null)";
        return os;
    }

    std::ostringstream ostr;
    llvm::raw_os_ostream ro(ostr);

    if (llvm::isa<llvm::Function>(val)) {
        ro << "FUNC " << val->getName().data();
    } else if (llvm::isa<llvm::BasicBlock>(val)) {
        ro << "label " << val->getName().data();
    } else {
        ro << *val;
    }

    ro.flush();

    // break the string if it is too long
    std::string str = ostr.str();
    if (str.length() > 100) {
        str.resize(40);
    }

    // escape the "
    size_t pos = 0;
    while ((pos = str.find('"', pos)) != std::string::npos) {
        str.replace(pos, 1, "\\\"");
        // we replaced one char with two, so we must shift after the new "
        pos += 2;
    }

    os << str;

    return os;
}

class LLVMDG2Dot : public debug::DG2Dot<LLVMNode>
{
public:

    LLVMDG2Dot(LLVMDependenceGraph *dg,
                  uint32_t opts = debug::PRINT_CFG | debug::PRINT_DD | debug::PRINT_CD,
                  const char *file = NULL)
        : debug::DG2Dot<LLVMNode>(dg, opts, file) {}

    /* virtual */
    std::ostream& printKey(std::ostream& os, llvm::Value *val)
    {
        return printLLVMVal(os, val);
    }

    /* virtual */
    bool checkNode(std::ostream& os, LLVMNode *node)
    {
        bool err = false;
        const llvm::Value *val = node->getKey();

        if (!val) {
            os << "\\nERR: no value in node";
            return true;
        }

        if (!node->getBBlock()
            && !llvm::isa<llvm::Function>(val)
            && !llvm::isa<llvm::GlobalVariable>(val)) {
            err = true;
            os << "\\nERR: no BB";
        }

        return err;
    }

    bool dump(const char *new_file = nullptr,
              const char *dump_func_only = nullptr)
    {
        // make sure we have the file opened
        if (!ensureFile(new_file))
            return false;

        const std::map<llvm::Value *,
                       LLVMDependenceGraph *>& CF = getConstructedFunctions();

        start();

        for (auto F : CF) {
            if (dump_func_only && !F.first->getName().equals(dump_func_only))
                continue;

            dumpSubgraph(F.second, F.first->getName().data());
        }

        end();

        return true;
    }

private:

    void dumpSubgraph(LLVMDependenceGraph *graph, const char *name)
    {
        dumpSubgraphStart(graph, name);

        for (auto B : graph->getBlocks()) {
            dumpBBlock(B.second);
        }

        for (auto B : graph->getBlocks()) {
            dumpBBlockEdges(B.second);
        }

        dumpSubgraphEnd(graph);
    }
};

class LLVMDGDumpBlocks : public debug::DG2Dot<LLVMNode>
{
public:

    LLVMDGDumpBlocks(LLVMDependenceGraph *dg,
                  uint32_t opts = debug::PRINT_CFG | debug::PRINT_DD | debug::PRINT_CD,
                  const char *file = NULL)
        : debug::DG2Dot<LLVMNode>(dg, opts, file) {}

    /* virtual
    std::ostream& printKey(std::ostream& os, llvm::Value *val)
    {
        return printLLVMVal(os, val);
    }
    */

    /* virtual */
    bool checkNode(std::ostream& os, LLVMNode *node)
    {
        return false; // no error
    }

    bool dump(const char *new_file = nullptr,
              const char *dump_func_only = nullptr)
    {
        // make sure we have the file opened
        if (!ensureFile(new_file))
            return false;

        const std::map<llvm::Value *,
                       LLVMDependenceGraph *>& CF = getConstructedFunctions();

        start();

        for (auto F : CF) {
            if (dump_func_only && !F.first->getName().equals(dump_func_only))
                continue;

            dumpSubgraph(F.second, F.first->getName().data());
        }

        end();

        return true;
    }

private:

    void dumpSubgraph(LLVMDependenceGraph *graph, const char *name)
    {
        dumpSubgraphStart(graph, name);

        for (auto B : graph->getBlocks()) {
            dumpBlock(B.second);
        }

        for (auto B : graph->getBlocks()) {
            dumpBlockEdges(B.second);
        }

        dumpSubgraphEnd(graph, false);
    }

    void dumpBlock(LLVMBBlock *blk)
    {
        out << "NODE" << blk << " [label=\"";

        std::ostringstream ostr;
        llvm::raw_os_ostream ro(ostr);

        ro << *blk->getKey();
        ro.flush();
        std::string str = ostr.str();

        unsigned int i = 0;
        unsigned int len = 0;
        while (str[i] != 0) {
            if (len >= 40) {
                str[i] = '\n';
                len = 0;
            } else
                ++len;

            if (str[i] == '\n')
                len = 0;

            ++i;
        }

        unsigned int slice_id = blk->getSlice();
        if (slice_id != 0)
            out << "\\nslice: "<< slice_id << "\\n";
        out << str << "\"";

        if (slice_id != 0)
            out << "style=filled fillcolor=greenyellow";

        out << "]\n";
    }

    void dumpBlockEdges(LLVMBBlock *blk)
    {
        for (const LLVMBBlock::BBlockEdge& edge : blk->successors()) {
            out << "NODE" << blk << " -> NODE" << edge.target
                << " [penwidth=2 label=\""<< (int) edge.label << "\"] \n";
        }

        for (const LLVMBBlock *pdf : blk->getPostDomFrontiers()) {
            out << "NODE" << blk << " -> NODE" << pdf
                << "[color=purple constraint=false]\n";
        }
    }
};
