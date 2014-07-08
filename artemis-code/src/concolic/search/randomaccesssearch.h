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
#include "explorationdescriptor.h"
#include "abstractselector.h"

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
    RandomAccessSearch(TraceNodePtr tree, AbstractSelectorPtr selector, uint searchBudget);

    bool chooseNextTarget();

    PathConditionPtr getTargetPC();
    QSet<SelectRestriction> getTargetDomConstraints();

    bool overUnexploredNode();

    void markNodeUnsat();
    void markNodeUnsolvable();
    void markNodeMissed();

public slots:
    void slNewTraceAdded(TraceNodePtr parent, int direction, TraceNodePtr suffix);

private:
    // The tree
    TraceNodePtr mTree;

    // The selector
    AbstractSelectorPtr mSelector;

    // The number of search attempts this class is allowed to make.
    uint mBudget;
    bool mUnlimitedBudget;

    // After a call to chooseNextTarget (which returned true), these hold the current state of the search position.
    ExplorationDescriptor mTarget;
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

    // Whether we have notified about the initial tree yet.
    bool mNotifiedFirstTrace;


    // The visitor part.
    // Should only be called by analyseTree().
    void visit(TraceNode* node);
    void visit(TraceConcreteBranch* node);
    void visit(TraceSymbolicBranch* node);
    void visit(TraceConcreteSummarisation *node);
    void visit(TraceMarker* node);
    void visit(TraceUnexplored* node);
    void visit(TraceAnnotation* node);
    void visit(TraceEnd* node);

};

} //namespace artemis

#endif // RANDOMACCESSSEARCH_H
