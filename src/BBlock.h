/// XXX add licence
//

#ifndef _BBLOCK_H_
#define _BBLOCK_H_

#include <cassert>
#include <list>

#include "ADT/DGContainer.h"
#include "analysis/Analysis.h"

#ifndef ENABLE_CFG
#error "BBlock.h needs be included with ENABLE_CFG"
#endif // ENABLE_CFG

namespace dg {

/// ------------------------------------------------------------------
// - BBlock
//     Basic block structure for dependence graph
/// ------------------------------------------------------------------
template <typename NodeT>
class BBlock
{
public:
    typedef typename NodeT::KeyType KeyT;
    typedef typename NodeT::DependenceGraphType DependenceGraphT;

    struct BBlockEdge {
        BBlockEdge(BBlock<NodeT>* t, uint8_t label = 0)
            : target(t), label(label) {}

        BBlock<NodeT> *target;
        // we'll have just numbers as labels now.
        // We can change it if there's a need
        uint8_t label;

        bool operator==(const BBlockEdge& oth) const
        {
            return target == oth.target && label == oth.label;
        }

        bool operator!=(const BBlockEdge& oth) const
        {
            return operator==(oth);
        }

        bool operator<(const BBlockEdge& oth) const
        {
            return target == oth.target ?
                        label < oth.label : target < oth.target;
        }
    };

    BBlock<NodeT>(NodeT *head = nullptr, DependenceGraphT *dg = nullptr)
        : key(KeyT()), dg(dg), ipostdom(nullptr), slice_id(0)
    {
        if (head) {
            append(head);
            assert(!dg || head->getDG() == nullptr || dg == head->getDG());
        }
    }

    typedef EdgesContainer<BBlock<NodeT>> BBlockContainerT;
    // we don't need labels with predecessors
    typedef EdgesContainer<BBlock<NodeT>> PredContainerT;
    typedef DGContainer<BBlockEdge> SuccContainerT;

    SuccContainerT& successors() { return nextBBs; }
    const SuccContainerT& successors() const { return nextBBs; }

    PredContainerT& predecessors() { return prevBBs; }
    const PredContainerT& predecessors() const { return prevBBs; }

    const BBlockContainerT& controlDependence() const { return controlDeps; }
    const BBlockContainerT& revControlDependence() const { return revControlDeps; }

    // similary to nodes, basic blocks can have keys
    // they are not stored anywhere, it is more due to debugging
    void setKey(const KeyT& k) { key = k; }
    const KeyT& getKey() const { return key; }

    // XXX we should do it a common base with node
    // to not duplicate this - something like
    // GraphElement that would contain these attributes
    void setDG(DependenceGraphT *d) { dg = d; }
    DependenceGraphT *getDG() const { return dg; }

    const std::list<NodeT *>& getNodes() const { return nodes; }
    std::list<NodeT *>& getNodes() { return nodes; }
    bool empty() const { return nodes.empty(); }
    size_t size() const { return nodes.size(); }

    void append(NodeT *n)
    {
        assert(n && "Cannot add null node to BBlock");

        n->setBasicBlock(this);
        nodes.push_back(n);
    }

    void prepend(NodeT *n)
    {
        assert(n && "Cannot add null node to BBlock");

        n->setBasicBlock(this);
        nodes.push_front(n);
    }

    bool hasControlDependence() const
    {
        return !controlDeps.empty();
    }

    // return true if all successors point
    // to the same basic block (not considering labels,
    // just the targets)
    bool successorsAreSame() const
    {
        if (nextBBs.size() < 2)
            return true;

        typename SuccContainerT::const_iterator start, iter, end;
        iter = nextBBs.begin();
        end = nextBBs.end();

        BBlock<NodeT> *block = iter->target;
        // iterate over all successor and
        // check if they are all the same
        for (++iter; iter != end; ++iter)
            if (iter->target != block)
                return false;

        return true;
    }

    // remove all edges from/to this BB and reconnect them to
    // other nodes
    void isolate()
    {
        // take every predecessor and reconnect edges from it
        // to successors
        for (auto pred : prevBBs) {
            // find the edge that is going to this node
            // and create new edges to all successors. The new edges
            // will have the same label as the found one
            DGContainer<BBlockEdge> new_edges;
            for (auto I = pred->nextBBs.begin(),E = pred->nextBBs.end(); I != E;) {
                auto cur = I++;
                if (cur->target == this) {
                    // create edges that will go from the predecessor
                    // to every successor of this node
                    for (const BBlockEdge& succ : nextBBs) {
                        // we cannot create an edge to this bblock (we're isolating _this_ bblock),
                        // that would be incorrect. It can occur when we're isolatin a bblock
                        // with self-loop
                        if (succ.target != this)
                            new_edges.insert(BBlockEdge(succ.target, cur->label));
                    }

                    // remove the edge from predecessor
                    pred->nextBBs.erase(*cur);
                }
            }

            // add newly created edges to predecessor
            for (const BBlockEdge& edge : new_edges)
                pred->addSuccessor(edge);
        }

        removeSuccessors();

        // we reconnected and deleted edges from other
        // BBs, but we still have edges from this to other BBs
        // NOTE: nextBBs were cleared in removeSuccessors()
        prevBBs.clear();

        // remove reverse edges to this BB
        for (auto B : controlDeps)
            B->revControlDeps.erase(this);

        controlDeps.clear();
    }

    void remove(bool with_nodes = true)
    {
        // do not leave any dangling reference
        isolate();

        if (dg)
            dg->removeBlock(key);

        // XXX what to do when this is entry block?

        if (with_nodes) {
            for (NodeT *n : nodes) {
                // we must set basic block to nullptr
                // otherwise the node will try to remove the
                // basic block again if it is of size 1
                n->setBasicBlock(nullptr);

                // remove dependency edges, let be CFG edges
                // as we'll destroy all the nodes
                n->removeCDs();
                n->removeDDs();
                // remove the node from dg
                n->removeFromDG();

                delete n;
            }
        }

        delete this;
    }

    void removeNode(NodeT *n) { nodes.remove(n); }

    size_t successorsNum() const { return nextBBs.size(); }
    size_t predecessorsNum() const { return prevBBs.size(); }

    bool addSuccessor(const BBlockEdge& edge)
    {
        bool ret = nextBBs.insert(edge);
        edge.target->prevBBs.insert(this);

        return ret;
    }

    bool addSuccessor(BBlock<NodeT> *b, uint8_t label = 0)
    {
        return addSuccessor(BBlockEdge(b, label));
    }

    void removeSuccessors()
    {
        // remove references to this node from successors
        for (const BBlockEdge& succ : nextBBs) {
            // This assertion does not hold anymore, since if we have
            // two edges with different labels to the same successor,
            // and we remove the successor, then we remove 'this'
            // from prevBBs twice. If we'll add labels even to predecessors,
            // this assertion must hold again
            // bool ret = succ.target->prevBBs.erase(this);
            // assert(ret && "Did not have this BB in successor's pred");
            succ.target->prevBBs.erase(this);
        }

        nextBBs.clear();
    }

    void removeSuccessor(const BBlockEdge& succ)
    {
        succ.target->prevBBs.erase(this);
        nextBBs.erase(succ);
    }

    void removePredecessors()
    {
        for (auto BB : prevBBs) {
            BB->nextBBs.erase(this);
        }

        prevBBs.clear();
    }

    bool addControlDependence(BBlock<NodeT> *b)
    {
        bool ret, ret2;

        // do not allow self-loops
        if (b == this)
            return false;

        ret = controlDeps.insert(b);
        ret2 = b->revControlDeps.insert(this);

        // we either have both edges or none
        assert(ret == ret2);

        return ret;
    }

    // get first node from bblock
    // or nullptr if the block is empty
    NodeT *getFirstNode() const
    {
        if (nodes.empty())
            return nullptr;

        return nodes.front();
    }

    // get last node from block
    // or nullptr if the block is empty
    NodeT *getLastNode() const
    {
        if (nodes.empty())
            return nullptr;

        return nodes.back();
    }

    // XXX: do this optional?
    BBlockContainerT& getPostDomFrontiers() { return postDomFrontiers; }
    const BBlockContainerT& getPostDomFrontiers() const { return postDomFrontiers; }
    BBlockContainerT& getRevPostDomFrontiers() { return revPostDomFrontiers; }
    const BBlockContainerT& getRevPostDomFrontiers() const { return revPostDomFrontiers; }

    bool addPostDomFrontier(BBlock<NodeT> *BB)
    {
        bool ret1, ret2;
        assert(BB && "passed nullptr as BB");

        ret1 = postDomFrontiers.insert(BB);
        ret2 = BB->revPostDomFrontiers.insert(this);

        // we either have both edges or none
        assert(ret1 == ret2);

        return ret1;
    }

    void setIPostDom(BBlock<NodeT> *BB)
    {
        assert(!ipostdom && "Already has the immedate post-dominator");
        ipostdom = BB;
        BB->postDominators.insert(this);
    }

    BBlock<NodeT> *getIPostDom() { return ipostdom; }
    const BBlock<NodeT> *getIPostDom() const { return ipostdom; }
    BBlockContainerT& getPostDominators() { return postDominators; }
    const BBlockContainerT& getPostDominators() const { return postDominators; }

    unsigned int getDFSOrder() const
    {
        return analysisAuxData.dfsorder;
    }

    // in order to fasten up interprocedural analyses,
    // we register all the call sites in the BBlock
    unsigned int getCallSitesNum() const
    {
        return callSites.size();
    }

    const std::set<NodeT *>& getCallSites()
    {
        return callSites;
    }

    bool addCallsite(NodeT *n)
    {
        assert(n->getBBlock() == this
               && "Cannot add callsite from different BB");

        return callSites.insert(n).second;
    }

    bool removeCallSite(NodeT *n)
    {
        assert(n->getBBlock() == this
               && "Removing callsite from different BB");

        return callSites.erase(n) != 0;
    }

    void setSlice(uint64_t sid)
    {
        slice_id = sid;
    }

    uint64_t getSlice() const { return slice_id; }

private:
    // optional key
    KeyT key;

    // reference to dg if needed
    DependenceGraphT *dg;

    // nodes contained in this bblock
    std::list<NodeT *> nodes;

    SuccContainerT nextBBs;
    PredContainerT prevBBs;

    // when we have basic blocks, we do not need
    // to keep control dependencies in nodes, because
    // all nodes in block has the same control dependence
    BBlockContainerT controlDeps;
    BBlockContainerT revControlDeps;

    // post-dominator frontiers
    BBlockContainerT postDomFrontiers;
    // reverse post-dominator frontiers
    BBlockContainerT revPostDomFrontiers;

    BBlock<NodeT> *ipostdom;
    // the post-dominator tree edges
    // (reverse to immediate post-dominator)
    BBlockContainerT postDominators;

    // is this block in some slice?
    uint64_t slice_id;

    // auxiliary data for analyses
    std::set<NodeT *> callSites;

    // auxiliary data for different analyses
    analysis::AnalysesAuxiliaryData analysisAuxData;
    friend class analysis::BBlockAnalysis<NodeT>;
};

} // namespace dg

#endif // _BBLOCK_H_
