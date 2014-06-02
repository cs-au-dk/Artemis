/*
 * Copyright 2012 Aarhus University
 *
 * Licensed under the GNU General Public License, Version 3 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *          http://www.gnu.org/licenses/gpl-3.0.html
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#ifndef RANDOMACCESSSEARCH_H
#define RANDOMACCESSSEARCH_H

#include <QPair>
#include <QMap>

#include "search.h"

namespace artemis
{

/**
 *  A base implementation for search strategies which wish to explore nodes in an arbitrary order.
 *
 *  The ideas is that this class provides the tree management service and an API for the actual search procedure to
 *  list nodes available for searching and then decide which one to explore next.
 *
 *  The search procedure would inherit from this class and implement nextTarget() to choose a next node.
 *  This class provides the interface required for TreeSearch and manages the tree itself.
 */

class RandomAccessSearch : public TreeSearch
{
public:
    RandomAccessSearch(TraceNodePtr tree);

    bool chooseNextTarget() final;

    PathConditionPtr getTargetPC() final;
    QSet<SelectRestriction> getTargetDomConstraints() final;

    bool overUnexploredNode() final;

    void markNodeUnsat() final;
    void markNodeUnsolvable() final;
    void markNodeMissed() final;

    // The visitor part.
    // Should only be called by analyseTree().
    // TODO: Could these be made private to enforce this?
    void visit(TraceNode* node);
    void visit(TraceConcreteBranch* node);
    void visit(TraceSymbolicBranch* node);
    void visit(TraceConcreteSummarisation *node);
    void visit(TraceMarker* node);
    void visit(TraceUnexplored* node);
    void visit(TraceAnnotation* node);
    void visit(TraceEnd* node);

protected:
    struct ExplorationDescriptor {
        // The parent branch of the unexplored node.
        TraceSymbolicBranchPtr branch;
        // The child of the branch which is unexplored.
        bool branchDirection;

        // Hash and equality operators so it can be put into sets, etc.
        friend inline bool operator==(const ExplorationDescriptor& a, const ExplorationDescriptor& b)
        {
            return a.branch == b.branch && a.branchDirection == b.branchDirection ;
        }

        friend inline uint qHash(const ExplorationDescriptor& key)
        {
            return ::qHash(key.branch) ^ ::qHash((int)key.branchDirection);
        }
    };

    /**
     *  Subclasses should override this method.
     *  possibleTargets is the set of ExplorationDescriptors representing every unexplored node in the graph.
     *  It returns a pair (success, nodeDescriptor) where success is true if we wish to continue exploration and false
     *  otherwise. If success is true, then nodeDescriptor must be a member of possibleTargets which is selected for
     *  exploration.
     */
    virtual QPair<bool, ExplorationDescriptor> nextTarget(QSet<ExplorationDescriptor> possibleTargets) = 0;

private:
    // The tree
    TraceNodePtr mTree;

    // After a call to chooseNextTarget (which returned true), these hold the current state of the search position.
    ExplorationDescriptor mTarget;
    PathConditionPtr mTargetPC;
    QSet<SelectRestriction> mTargetDomConstraints;

    // A table of parent pointers (between symbolic branches), used to build the PC for a given ExplorationDescriptor.
    // Maps a symbolic branch to it's parent sym branch and the direction taken from the parent to reach this node.
    QMap<TraceSymbolicBranchPtr, QPair<TraceSymbolicBranchPtr, bool> > mBranchParents;
    // A table of parent pointers between marker nodes, used to build the DOM constraints.
    QMap<TraceMarkerPtr, TraceMarkerPtr> mMarkerParents;
    // A table mapping symbolic branches to their parent (i.e. nearest ancestor) marker node.
    QMap<TraceSymbolicBranchPtr, TraceMarkerPtr> mBranchParentMarkers;

    // The set of possible explorations of the current tree.
    QSet<ExplorationDescriptor> mPossibleExplorations;

    // Scan the whole tree and build the list of possible explorations and the parent pointer table.
    // TODO: To fully rescan the tree like this is needlessly inefficient.
    // Instead we really should have the trace merger notify the search procedure of where the tree was extended.
    // Then mBranchParents, mPossibleExplorations etc. could be updated incrementally.
    // Alternatively, we could just analyse all of the possible exploration targets from the previous call.
    void analyseTree();

    // Temp variables used by the visitors.
    TraceSymbolicBranchPtr mCurrentBranchParent;
    bool mCurrentBranchParentDirection;
    TraceMarkerPtr mCurrentMarkerParent;
    TraceNodePtr mThisNode; // Tracks a smart pointer vaersion of 'this' throughout the visitor.
    void analyseNode(TraceNodePtr node);

    // Helpers for chooseNextTarget
    PathConditionPtr calculatePC(ExplorationDescriptor target);
    QSet<SelectRestriction> calculateDomConstraints(ExplorationDescriptor target);
};


} //namespace artemis

#endif // RANDOMACCESSSEARCH_H
