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

#ifndef SEARCHDFS_H
#define SEARCHDFS_H

#include <QStack>
#include <QPair>

#include "search.h"
#include "concolic/pathcondition.h"


namespace artemis
{



/**
 *  Implements the path tree search with DFS.
 *  (Strictly something like iterative deepening, see below.)
 *
 *  Usage:
 *      chooseNextTarget() can be called to find the next unexplored node in the tree.
 *      It returns true if the search is over an unexplored node, or false when we reach the end of the search.
 *      Once the tree has been explored at a certain depth, the depth limit is increased and the search restarted a
 *      certain number of times.
 *
 *  Note that the implementation of this class relies on the fact that pointers to branch nodes in the tree
 *  will still be valid between calls. When merging new traces into the tree (or any other operations) it is essential
 *  that the tree is only extended and not modified (removing TraceUnexplored nodes in particular is fine).
 */

class DepthFirstSearch : public QObject, public TreeSearch
{
    Q_OBJECT

public:
    DepthFirstSearch(TraceNodePtr tree, unsigned int depthLimit, unsigned int restartLimit);

    // Selects an unexplored node from the tree to be explored next.
    bool chooseNextTarget();

    // Retrieves the PC of any target node which was selected.
    PathConditionPtr getTargetPC();

    // Retrieves the DOM constraints of any target node which was selected.
    QSet<SelectRestriction> getTargetDomConstraints();

    // Returns a description of the target which can be looked up later.
    ExplorationDescriptor getTargetDescriptor();

    // The depth limit for our DFS.
    void setDepthLimit(unsigned int depth);
    unsigned int getDepthLimit();


    // The visitor part which does the actual searching.
    void visit(TraceNode* node);            // Abstract nodes. An error if we reach this.
    void visit(TraceConcreteBranch* node);
    void visit(TraceSymbolicBranch* node);
    void visit(TraceConcreteSummarisation *node);
    void visit(TraceMarker* node);
    void visit(TraceUnexplored* node);
    void visit(TraceUnexploredMissed* node);
    void visit(TraceUnexploredUnsat* node);
    void visit(TraceUnexploredUnsolvable* node);
    void visit(TraceUnexploredQueued* node);
    void visit(TraceAnnotation* node);      // Ignore all other annotations.
    void visit(TraceEnd* node);             // Stop searching at *any* end node.

public slots:
    void slNewTraceAdded(TraceNodePtr parent, int direction, TraceNodePtr suffix, TraceNodePtr fullTrace);

protected:
    // Restart a fresh search from the beginning of the tree.
    void restartSearch();
    bool deepenRestartAndChoose();

private:
    // The root of the tree we are searching.
    TraceNodePtr mTree;

    // The maximum depth (in symbolic branches only) that we will search in the tree.
    unsigned int mDepthLimit;
    unsigned int mInitialDepthLimit;
    unsigned int mCurrentDepth;

    // Controls how many times we are allowed to deepen the search.
    unsigned int mRestartsRemaining;
    bool mUnlimitedRestarts;

    // Used to end the search once we have explored all nodes.
    bool mPreviousPassFoundTarget;
    bool mNothingRemainsToExplore;

    // The PC which is accumulated as we move down the tree.
    // Note that we do not store the PC directly but instead keep a list of branches, which allows PathCondition::createFromBranchList to build the PC intelligently.
    PathBranchList mCurrentPC;

    // The dynamic DOM constraints which are accumulated as we move down the tree.
    QSet<SelectRestriction> mCurrentDomConstraints;

    // Stores whether or not the iteration is finished.
    bool mFoundTarget;

    // We store the position which we left off the search on the previous call to chooseNextTarget.
    // We store the parent branch of the unexplored node and the "direction" (i.e. true or false branch)
    // of that node which was unexplored.
    // This allows us to easily re-start the search and/or check whether an attept worked correctly.
    // N.B. mPreviousParent may not be in mParentStack if we are currently exploring its right branch.
    bool mIsPreviousRun;
    TraceBranch* mPreviousParent;
    bool mPreviousDirection;

    // A stack of the ancestor branch nodes to the current position in the search.
    // Each ancestor node is paired with its depth in the tree and the PC up to that point.
    // This is used for backtracking during the DFS.
    // N.B. We could avoid this if we included parent pointers in the tree, but this would involve some iterative traversal, going against the idea of using a visitor in the first place!
    // Exactly one of node and summaryNode should be non-null. childrenVisited is only valid for summaryNode.
    struct SavedPosition {
        SavedPosition(){}
        SavedPosition(TraceBranch* node, unsigned int depth, PathBranchList condition, QSet<SelectRestriction> domConstraints) : node(node), depth(depth), condition(condition), domConstraints(domConstraints), summaryNode(NULL), childrenVisited(1) {}
        SavedPosition(TraceConcreteSummarisation* summaryNode, unsigned int depth, PathBranchList condition, QSet<SelectRestriction> domConstraints, int childrenVisited) : node(NULL), depth(depth), condition(condition), domConstraints(domConstraints), summaryNode(summaryNode), childrenVisited(childrenVisited) {}

        TraceBranch* node;

        unsigned int depth;
        PathBranchList condition; // Condition to reach this node, not including the symbolic condition of this particular node if it is symbolic.
        QSet<SelectRestriction> domConstraints;

        TraceConcreteSummarisation* summaryNode;
        int childrenVisited;
    };
    QStack<SavedPosition> mParentStack;

    // Helper methods for the visitors.
    void continueFromLeaf();
    TraceNodePtr nextAfterLeaf();

    // This is a hack used by getTargetDescriptor() and visit(TraceUnexplored)
    ExplorationDescriptor getCurrentExplorationDescriptor(TraceSymbolicBranch* parent);
    static void pointerDeleterNoOp(TraceSymbolicBranch* branch) {}

    // Used to check for traces inserted "behind" the search cursor during a search.
    bool mTreeHasNewTrace;
};




}

#endif // SEARCHDFS_H
