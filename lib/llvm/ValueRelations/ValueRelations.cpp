#include "dg/llvm/ValueRelations/ValueRelations.h"
#ifndef NDEBUG
#include <iostream>
#endif
namespace dg {
namespace vr {

// *********************** general between *************************** //
Relations ValueRelations::_between(Handle lt, Handle rt) const {
    return graph.getRelated(lt, allRelations)[rt];
}
Relations ValueRelations::_between(Handle lt, V rt) const {
    HandlePtr mRt = maybeGet(rt);
    if (mRt)
        return _between(lt, *mRt);

    return _between(lt, llvm::dyn_cast<BareC>(rt));
}
Relations ValueRelations::_between(Handle lt, C cRt) const {
    if (!cRt)
        return {};

    for (Relations::Type rel :
         {Relations::SLE, Relations::ULE, Relations::SGE, Relations::UGE}) {
        C boundLt;
        Relations relsLt;
        std::tie(boundLt, relsLt) = getBound(lt, Relations().set(rel));

        if (!boundLt)
            continue;

        Relations relsBound = compare(boundLt, cRt);
        // lt <= boundLt <= cRt || lt >= boundLt >= cRt
        if (relsBound.has(rel))
            return compose(relsLt, relsBound);
    }
    return {};
}
Relations ValueRelations::_between(V lt, Handle rt) const {
    return _between(rt, lt).invert();
}
Relations ValueRelations::_between(C lt, Handle rt) const {
    return _between(rt, lt).invert();
}
Relations ValueRelations::_between(V lt, V rt) const {
    if (lt == rt)
        return Relations().eq().addImplied();

    if (HandlePtr mLt = maybeGet(lt))
        return _between(*mLt, rt);

    if (HandlePtr mRt = maybeGet(rt))
        return _between(llvm::dyn_cast<BareC>(lt), *mRt);

    C cLt = llvm::dyn_cast<BareC>(lt);
    C cRt = llvm::dyn_cast<BareC>(rt);

    if (!cLt || !cRt)
        return {};
    return compare(cLt, cRt);
}

// *************************** iterators ****************************** //
ValueRelations::rel_iterator
ValueRelations::begin_related(V val, const Relations &rels) const {
    assert(valToBucket.find(val) != valToBucket.end());
    Handle h = valToBucket.find(val)->second;
    return {*this, h, rels};
}

ValueRelations::rel_iterator ValueRelations::end_related(V /*val*/) const {
    return rel_iterator(*this);
}

ValueRelations::RelGraph::iterator
ValueRelations::begin_related(Handle h, const Relations &rels) const {
    return graph.begin_related(h, rels);
}

ValueRelations::RelGraph::iterator ValueRelations::end_related(Handle h) const {
    return graph.end_related(h);
}

ValueRelations::plain_iterator ValueRelations::begin() const {
    return {bucketToVals.begin(), bucketToVals.end()};
}

ValueRelations::plain_iterator ValueRelations::end() const {
    return {bucketToVals.end()};
}

ValueRelations::RelGraph::iterator
ValueRelations::begin_buckets(const Relations &rels) const {
    return graph.begin(rels);
}

ValueRelations::RelGraph::iterator ValueRelations::end_buckets() const {
    return graph.end();
}

// ****************************** get ********************************* //
ValueRelations::HandlePtr ValueRelations::maybeGet(V val) const {
    auto found = valToBucket.find(val);
    return (found == valToBucket.end() ? nullptr : &found->second.get());
}

std::pair<ValueRelations::BRef, bool> ValueRelations::get(V val) {
    if (HandlePtr mh = maybeGet(val))
        return {*mh, false};
    Handle newH = graph.getNewBucket();
    return add(val, newH);
}

ValueRelations::V ValueRelations::getAny(Handle h) const {
    auto found = bucketToVals.find(h);
    assert(found != bucketToVals.end() && !found->second.empty());
    return *found->second.begin();
}

ValueRelations::C ValueRelations::getAnyConst(Handle h) const {
    for (V val : bucketToVals.find(h)->second) {
        if (C c = llvm::dyn_cast<BareC>(val))
            return c;
    }
    return nullptr;
}

const VectorSet<ValueRelations::V> &ValueRelations::getEqual(Handle h) const {
    return bucketToVals.find(h)->second;
}

VectorSet<ValueRelations::V> ValueRelations::getEqual(V val) const {
    HandlePtr mH = maybeGet(val);
    if (!mH)
        return {val};
    return getEqual(*mH);
}

std::vector<ValueRelations::V>
ValueRelations::getDirectlyRelated(V val, const Relations &rels) const {
    HandlePtr mH = maybeGet(val);
    if (!mH)
        return {};
    RelationsMap related = graph.getRelated(*mH, rels, true);

    std::vector<ValueRelations::V> result;
    std::transform(related.begin(), related.end(), std::back_inserter(result),
                   [this](const RelationsMap::value_type &pair) {
                       return this->getAny(pair.first);
                   });
    return result;
}

std::pair<ValueRelations::C, Relations>
ValueRelations::getBound(Handle h, Relations rels) const {
    RelationsMap related = graph.getRelated(h, rels);

    C resultC = nullptr;
    Relations resultR;
    for (const auto &pair : related) {
        C c = getAnyConst(pair.first);
        if (c && (!resultC || compare(c, rels, resultC))) {
            resultC = c;
            resultR = pair.second;
        }
    }

    return {resultC, resultR};
}

std::pair<ValueRelations::C, Relations>
ValueRelations::getBound(V val, Relations rel) const {
    HandlePtr mH = maybeGet(val);
    if (!mH)
        return {llvm::dyn_cast<BareC>(val), Relations().eq()};

    return getBound(*mH, rel);
}

ValueRelations::C ValueRelations::getLesserEqualBound(V val) const {
    return getLowerBound(val).first;
}

ValueRelations::C ValueRelations::getGreaterEqualBound(V val) const {
    return getUpperBound(val).first;
}

ValueRelations::HandlePtr ValueRelations::getHandleByPtr(Handle h) {
    if (!h.hasRelation(Relations::PT))
        return nullptr;
    return &h.getRelated(Relations::PT);
}

VectorSet<ValueRelations::V> ValueRelations::getValsByPtr(V from) const {
    HandlePtr mH = maybeGet(from);
    if (!mH)
        return {};
    HandlePtr toH = getHandleByPtr(*mH);
    if (!toH)
        return {};
    return getEqual(*toH);
}

ValueRelations::Handle ValueRelations::getHandle(V val) const {
    HandlePtr mH = maybeGet(val);
    assert(mH);
    return *mH;
}

// ************************** placeholder ***************************** //
void ValueRelations::erasePlaceholderBucket(Handle h) {
    auto found = bucketToVals.find(h);
    assert(found != bucketToVals.end());
    for (V val : found->second) {
        assert(valToBucket.find(val) != valToBucket.end() &&
               valToBucket.at(val) == h);
        valToBucket.erase(val);
    }
    bucketToVals.erase(h);
    graph.erase(h);
}

// ***************************** other ******************************** //
bool ValueRelations::compare(C lt, Relations::Type rel, C rt) {
    return compare(lt, rt).has(rel);
}

bool ValueRelations::compare(C lt, Relations rels, C rt) {
    return compare(lt, rt).anyCommon(rels);
}

Relations ValueRelations::compare(C lt, C rt) {
    // ignore bool values
    if ((lt->getBitWidth() == 1 || rt->getBitWidth() == 1) &&
        lt->getBitWidth() != rt->getBitWidth())
        return {};
    int64_t isLt = lt->getSExtValue();
    int64_t isRt = rt->getSExtValue();
    Relations result;
    if (isLt < isRt)
        result.slt();
    else if (isLt > isRt)
        result.sgt();
    else
        result.eq();

    // possible to collect unsigned relations between constants here

    return result.addImplied();
}

bool ValueRelations::holdsAnyRelations() const {
    return !valToBucket.empty() && !graph.empty();
}

ValueRelations::HandlePtr
ValueRelations::getCorrespondingBorder(const ValueRelations &other,
                                       Handle otherH) {
    HandlePtr result = nullptr;
    for (auto otherRel : other.getRelated(otherH, Relations().sle().sge())) {
        if (otherRel.second.has(Relations::EQ))
            continue;

        const llvm::Value *arg =
                V(other.getInstance<llvm::Argument>(otherRel.first));
        if (!arg)
            continue;

        for (auto thisRel : getRelated(arg, otherRel.second.invert())) {
            if (getEqual(thisRel.first).empty() &&
                !has(thisRel.first, Relations::PF)) {
                // if (result)
                //     return nullptr;
                assert(!result);
                result = &thisRel.first.get();
            }
        }
    }
    return result;
}

ValueRelations::HandlePtr
ValueRelations::getCorresponding(const ValueRelations &other, Handle otherH,
                                 const VectorSet<V> &otherEqual) {
    if (otherEqual.empty()) { // other is a placeholder bucket, therefore it is
                              // pointed to from other bucket
        if (!otherH.hasRelation(Relations::PF)) {
            HandlePtr thisH = getCorrespondingBorder(other, otherH);
            return thisH ? thisH : &newPlaceholderBucket();
        }
        assert(otherH.hasRelation(Relations::PF));
        Handle otherFromH = otherH.getRelated(Relations::PF);
        HandlePtr thisFromH = getCorresponding(other, otherFromH);
        if (!thisFromH)
            return nullptr;

        Handle h = newPlaceholderBucket(*thisFromH);
        bool ch = graph.addRelation(*thisFromH, Relations::PT, h);
        updateChanged(ch);
        return &h;
    }

    // otherwise find unique handle for all equal elements from other
    HandlePtr mH = nullptr;
    for (V val : otherEqual) {
        HandlePtr oH = maybeGet(val);
        if (!mH) // first handle found
            mH = oH;
        else if (oH && oH != mH) { // found non-equal handle in this
            if (hasConflictingRelation(*oH, *mH, Relations::EQ))
                return nullptr;
            set(*oH, Relations::EQ, *mH);
            mH = maybeGet(val); // update possibly invalidated handle
            assert(mH);
        }
    }
    return mH ? mH : &add(otherEqual.any(), graph.getNewBucket()).first.get();
}

ValueRelations::HandlePtr
ValueRelations::getCorresponding(const ValueRelations &other, Handle otherH) {
    return getCorresponding(other, otherH, other.getEqual(otherH));
}

ValueRelations::HandlePtr
ValueRelations::getAndMerge(const ValueRelations &other, Handle otherH) {
    const VectorSet<V> &otherEqual = other.getEqual(otherH);
    HandlePtr thisH = getCorresponding(other, otherH, otherEqual);

    if (!thisH)
        return nullptr;

    for (V val : otherEqual)
        add(val, *thisH);

    return thisH;
}

bool ValueRelations::merge(const ValueRelations &other, Relations relations) {
    bool noConflict = true;
    for (const auto &edge : other.graph) {
        if (!relations.has(edge.rel()) ||
            (edge.rel() == Relations::EQ && !other.hasEqual(edge.to())))
            continue;

        HandlePtr thisToH = getAndMerge(other, edge.to());
        HandlePtr thisFromH = getCorresponding(other, edge.from());

        if (!thisToH || !thisFromH) {
            noConflict = false;
            continue;
        }

        if (!graph.haveConflictingRelation(*thisFromH, edge.rel(), *thisToH)) {
            bool ch = graph.addRelation(*thisFromH, edge.rel(), *thisToH);
            updateChanged(ch);
        } else
            noConflict = false;
    }
    return noConflict;
}

void ValueRelations::add(V val, Handle h, VectorSet<V> &vals) {
    ValToBucket::iterator it = valToBucket.lower_bound(val);
    // val already bound to a handle
    if (it != valToBucket.end() && !(valToBucket.key_comp()(val, it->first))) {
        // it is already bound to passed handle
        if (it->second == h)
            return;
        V oldVal = it->first;
        Handle oldH = it->second;
        assert(bucketToVals.find(oldH) != bucketToVals.end());
        assert(bucketToVals.at(oldH).find(oldVal) !=
               bucketToVals.at(oldH).end());
        bucketToVals.find(oldH)->second.erase(oldVal);
        it->second = h;
    } else
        valToBucket.emplace_hint(it, val, h);

    assert(valToBucket.find(val)->second == h);
    vals.emplace(val);
    updateChanged(true);
}

std::pair<ValueRelations::BRef, bool> ValueRelations::add(V val, Handle h) {
    add(val, h, bucketToVals[h]);

    C c = llvm::dyn_cast<BareC>(val);
    if (!c)
        return {h, false};

    for (auto &pair : bucketToVals) {
        if (pair.second.empty())
            continue;

        Handle otherH = pair.first;
        if (C otherC = getAnyConst(otherH)) {
            if (compare(c, Relations::EQ, otherC)) {
                graph.addRelation(h, Relations::EQ, otherH);
                assert(valToBucket.find(val) != valToBucket.end());
                return {valToBucket.find(val)->second, true};
            }

            for (Relations::Type type : {Relations::SLT, Relations::ULT,
                                         Relations::SGT, Relations::UGT}) {
                if (compare(c, type, otherC))
                    graph.addRelation(h, type, otherH);
            }
        }
    }

    return {h, false};
}

void ValueRelations::areMerged(Handle to, Handle from) {
    VectorSet<V> &toVals = bucketToVals.find(to)->second;
    assert(bucketToVals.find(from) != bucketToVals.end());
    const VectorSet<V> fromVals = bucketToVals.find(from)->second;

    for (V val : fromVals)
        add(val, to, toVals);

    assert(bucketToVals.at(from).empty());
    bucketToVals.erase(from);
}

std::string strip(std::string str, size_t skipSpaces) {
    assert(!str.empty() && !std::isspace(str[0]));

    size_t lastIndex = 0;
    for (size_t i = 0; i < skipSpaces; ++i) {
        size_t nextIndex = str.find(' ', lastIndex + 1);
        if (nextIndex == std::string::npos)
            return str;
        lastIndex = nextIndex;
    }
    return str.substr(0, lastIndex);
}

#ifndef NDEBUG
void dump(std::ostream &out, ValueRelations::Handle h,
          const ValueRelations::BucketToVals &map) {
    auto found = map.find(h);
    assert(found != map.end());
    const VectorSet<ValueRelations::V> &vals = found->second;

    out << "{{ ";
    if (vals.empty())
        out << "placeholder ";
    else
        for (ValueRelations::V val : vals)
            out << (val == *vals.begin() ? "" : " | ")
                << strip(debug::getValName(val), 4);
    out << " }}";
}

std::ostream &operator<<(std::ostream &out, const ValueRelations &vr) {
    for (const auto &edge : vr.graph) {
        if (edge.rel() == Relations::EQ) {
            if (!edge.to().hasAnyRelation()) {
                out << "              ";
                dump(out, edge.to(), vr.bucketToVals);
                out << "\n";
            }
            continue;
        }
        out << "    " << edge << "    ";
        dump(out, edge.from(), vr.bucketToVals);
        out << " " << edge.rel() << " ";
        dump(out, edge.to(), vr.bucketToVals);
        out << "\n";
    }
    return out;
}
#endif
} // namespace vr
} // namespace dg
