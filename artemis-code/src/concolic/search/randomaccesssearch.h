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

class RandomAccessSearch : public QObject, public TreeSearch
{
    Q_OBJECT

public:
    RandomAccessSearch(TraceNodePtr tree, uint searchBudget);

    bool chooseNextTarget() final;

    PathConditionPtr getTargetPC() final;
    QSet<SelectRestriction> getTargetDomConstraints() final;

    bool overUnexploredNode() final;

    void markNodeUnsat() final;
    void markNodeUnsolvable() final;
    void markNodeMissed() final;

    // The visitor part.
    // Should only be called by analyseTree().
    void visit(TraceNode* node) final;
    void visit(TraceConcreteBranch* node) final;
    void visit(TraceSymbolicBranch* node) final;
    void visit(TraceConcreteSummarisation *node) final;
    void visit(TraceMarker* node) final;
    void visit(TraceUnexplored* node) final;
    void visit(TraceAnnotation* node) final;
    void visit(TraceEnd* node) final;

public slots:
    void slNewTraceAdded(TraceNodePtr parent, int direction, TraceNodePtr suffix);

protected:
    struct ExplorationDescriptor {
        // The parent branch of the unexplored node.
        TraceSymbolicBranchPtr branch;
        // The child of the branch which is unexplored.
        bool branchDirection;

        // Information which is useful to one or more of the subclasses:
        unsigned int symbolicDepth;

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
    virtual QPair<bool, ExplorationDescriptor> nextTarget(QList<ExplorationDescriptor> possibleTargets) = 0;

    /**
     *  Subclasses may override this method to be notifid when a new trace suffix is added to the tree.
     *  Note that this method may not always be called between calls to nextTarget().
     *  parent is the branch where the new trace split off from the existing tree.
     *  It can be a concrete branch, symbolic branch or concrete summary.
     *  direction is the direction from that node where the new trace was added.
     *  suffix is the newly added part of the trace itself.
     */
    virtual void newTraceAdded(TraceNodePtr parent, int direction, TraceNodePtr suffix) {}

    /**
     *  These functions may be used if the subclasses need to be notified about other types of modification to the tree.
     *  The modification itself is done by this helper.
     */
    virtual void newUnsat(ExplorationDescriptor node) {}
    virtual void newUnsolvable(ExplorationDescriptor node) {}
    virtual void newMissed(ExplorationDescriptor node) {}

private:
    // The tree
    TraceNodePtr mTree;

    // The number of search attempts this class is allowed to make.
    uint mBudget;
    bool mUnlimitedBudget;

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
    QList<ExplorationDescriptor> mPossibleExplorations;

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
    unsigned int mCurrentSymbolicDepth;
    TraceNodePtr mThisNode; // Tracks a smart pointer vaersion of 'this' throughout the visitor.
    void analyseNode(TraceNodePtr node);

    // Helpers for chooseNextTarget
    PathConditionPtr calculatePC(ExplorationDescriptor target);
    QSet<SelectRestriction> calculateDomConstraints(ExplorationDescriptor target);
};


} //namespace artemis

#endif // RANDOMACCESSSEARCH_H
