#ifndef _DG_MARKERSRGBUILDERFS_H
#define _DG_MARKERSRGBUILDERFS_H

#include <memory>
#include <vector>
#include <unordered_set>
#include <unordered_map>
#include <map>

#include "analysis/BFS.h"
#include "analysis/ReachingDefinitions/Srg/SparseRDGraphBuilder.h"
#include "analysis/ReachingDefinitions/Srg/IntervalMap.h"

namespace dg {
namespace analysis {
namespace rd {
namespace srg {

class MarkerSRGBuilderFS : public SparseRDGraphBuilder
{
    /* see using-s in SparseRDGraphBuilder for reference... */

    // offset in variable
    using OffsetT = uint64_t;
    using Intervals = std::vector<detail::Interval>;

    // for each variable { for each block { for each offset in variable { remember definition } } }
    using DefMapT = std::unordered_map<NodeT *, std::unordered_map<BlockT *, detail::IntervalMap<NodeT *>>>;

    /* the resulting graph - stored in class for convenience, moved away on return */
    SparseRDGraph srg;

    /* phi nodes added during the process */
    std::vector<std::unique_ptr<NodeT>> phi_nodes;

    /* work structures for strong defs */
    DefMapT current_def;
    DefMapT last_def;

    /* work structure for weak defs */
    DefMapT weak_def;

    void writeVariableStrong(const DefSite& var, NodeT *assignment, BlockT *block);
    void writeVariableWeak(const DefSite& var, NodeT *assignment, BlockT *block);
    NodeT *readVariableRecursive(const DefSite& var, BlockT *block, const Intervals& covered);

    std::vector<NodeT *> readVariable(const DefSite& var, BlockT *read) {
        Intervals empty_vector;
        return readVariable(var, read, empty_vector);
    }

    std::vector<NodeT *> readVariable(const DefSite& var, BlockT *read, const Intervals& covered);

    void addPhiOperands(const DefSite& var, NodeT *phi, BlockT *block, const Intervals& covered);

    void insertSrgEdge(NodeT *from, NodeT *to, const DefSite& var) {
        srg[from].push_back(std::make_pair(var, to));
    }

    void performLvn(BlockT *block) {
        for (NodeT *node : block->getNodes()) {

            for (const DefSite& def : node->defs) {
                if (node->isOverwrite(def) && def.len != 0 && def.offset != UNKNOWN_OFFSET)
                    last_def[def.target][block].add(detail::Interval{def.offset, def.len}, node);
                else
                    writeVariableWeak(def, node, block);
            }
        }
    }

    void performGvn(BlockT *block) {

        for (NodeT *node : block->getNodes()) {

            for (const DefSite& use : node->getUses()) {
                std::vector<NodeT *> assignments = readVariable(use, block);
                // add edge from last definition to here
                for (NodeT *assignment : assignments) {
                    insertSrgEdge(assignment, node, use);
                }
            }

            for (const DefSite& def : node->defs) {
                if (node->isOverwrite(def) && def.len != 0 && def.offset != UNKNOWN_OFFSET)
                    writeVariableStrong(def, node, block);
            }
        }
    }

public:

    std::pair<SparseRDGraph, std::vector<std::unique_ptr<NodeT>>>
        build(NodeT *root) override {

        current_def.clear();

        BBlockBFS<NodeT> bfs(BFS_BB_CFG | BFS_INTERPROCEDURAL);

        AssignmentFinder af;
        af.populateUnknownMemory(root);

        std::vector<BlockT *> cfg;
        BlockT *block = root->getBBlock();
        bfs.run(block, [&,this](BlockT *block, void*){
            cfg.push_back(block);
        }, nullptr);

        for (BlockT *BB : cfg) {
            performLvn(BB);
        }

        for (BlockT *BB : cfg) {
            performGvn(BB);
        }

        return std::make_pair<SparseRDGraph, std::vector<std::unique_ptr<NodeT>>>(std::move(srg), std::move(phi_nodes));
    }

};

}
}
}
}

#endif /* _DG_MARKERSRGBUILDERFS_H */
