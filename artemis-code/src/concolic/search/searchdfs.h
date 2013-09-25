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
 *
 *  Usage:
 *      chooseNextTarget() can be called to find the next unexplored node in the tree.
 *      It returns either a pointer to an unexplored node, or a null pointer when we reach the end of the tree.
 *      Once this happens we have the option to restart, possibly increasing the search depth as well.
 *
 *  Note that the implementation of this class relies on the fact that pointers to branch nodes in the tree
 *  will still be valid between calls. When merging new traces into the tree (or any other operations) it is essential
 *  that the tree is only extended and not modified (removing TraceUnexplored nodes in particular is fine).
 */

class DepthFirstSearch : TreeSearch
{
public:
    DepthFirstSearch(TraceNodePtr tree, unsigned int depthLimit = 5); // TODO: what is a sensible default?

    // Selects an unexplored node from the tree to be explored next.
    bool chooseNextTarget();

    // Retrieves the PC of any target node which was selected.
    PathConditionPtr getTargetPC();

    // The depth limit for our DFS.
    void setDepthLimit(unsigned int depth);
    unsigned int getDepthLimit();

    // Restart a fresh search from the beginning of the tree.
    void restartSearch();

    // When over an unexplored node, we may mark it as "attempted but failed to explore".
    // This can be used in later "passes" of the search to avoid wasting time on unreachable nodes or guide the search intelligently.
    // TODO: Currently it is not, and is only used in TraceDisplay to show the user what is going on.
    bool overUnexploredNode();
    void markNodeUnsat();
    void markNodeUnsolvable();
    void markNodeMissed();

    // The visitor part which does the actual searching.
    void visit(TraceNode* node);            // Abstract nodes. An error if we reach this.
    void visit(TraceConcreteBranch* node);
    void visit(TraceSymbolicBranch* node);
    void visit(TraceUnexplored* node);
    void visit(TraceAnnotation* node);      // Ignore all annotations.
    void visit(TraceEnd* node);             // Stop searching at *any* end node.

private:
    // The root of the tree we are searching.
    TraceNodePtr mTree;

    // The maximum depth (in branches only) that we will search in the tree.
    unsigned int mDepthLimit;
    unsigned int mCurrentDepth;

    // The PC which is accumulated as we move down the tree.
    PathConditionPtr mCurrentPC;

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
    struct SavedPosition {
        SavedPosition(){}
        SavedPosition(TraceBranch* node, unsigned int depth, PathCondition condition) : node(node), depth(depth), condition(condition) {}
        TraceBranch* node;
        unsigned int depth;
        PathCondition condition; // Condition to reach this node, not including the symbolic condition of this particular node if it is symbolic.
    };
    QStack<SavedPosition> mParentStack;

    // Helper methods for the visitors.
    void continueFromLeaf();
    TraceNodePtr nextAfterLeaf();
};

typedef QSharedPointer<DepthFirstSearch> DepthFirstSearchPtr;



}

#endif // SEARCHDFS_H
