/*
 * Copyright 2012 Aarhus University
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include "searchdfs.h"
#include "util/loggingutil.h"
#include <assert.h>

namespace artemis
{



DepthFirstSearch::DepthFirstSearch(TraceNodePtr tree, unsigned int depthLimit) :
    mTree(tree),
    mDepthLimit(depthLimit),
    mCurrentDepth(0),
    mIsPreviousRun(false)
{
}


/**
 *  Selects an unexplored node from the tree to be explored next.
 *  Calculates the constraint [hopefully] leading to the unexplored node it has chosen.
 *  Returns true if an unexplored node was found (then the constraint can be retrieved with getTargetPC())
 *  and false when we reached the end of the tree.
 *  N.B. in this case there may still be unexplored areas in the following cases:
 *      * They were lower than the current search depth in the tree.
 *      * They were skipped (i.e. the first attempt to explore them failed).
 *      * A previously skipped node was explored "accidentally" by a later run.
 *
 *  TODO: I think this mehtod assumes there will be at least one branch above any unexplored node.
 *        This means we should only run it on a tree containing at least one trace for now.
 */
bool DepthFirstSearch::chooseNextTarget()
{
    TraceNodePtr current;

    // Check if we are starting a new search or continuing an old one.
    if(mIsPreviousRun){
        // Continue the search.
        
        // Check if the left/right (according to mPreviousDirection) child of mPreviousParent is still unexplored.
        // If so, skip it and search for the next unexplored node.
        // If not, we want to search the newly revealed area before continuing.
        // ASSUMPTION: if the true/false child of a branch eventually terminates in unexplored (without further branching) then it is immediately unexplored.

        if(mPreviousDirection){
            // We are interested in the 'true' branch of mPreviousParent.
            current = mPreviousParent->getTrueBranch();
        }else{
            // We are interested in the 'false' branch of mPreviousParent.
            current = mPreviousParent->getFalseBranch();
        }
        // The depth, PC, etc. are all already set from the previous call.


        if(isImmediatelyUnexplored(current)){
            // Then the previous run did not reach the intended target.
            // Use the same method as continueFromLeaf() to jump to the next node to be searched.
            current = nextAfterLeaf();
        }

    }else{
        // Strat a new search.
        current = mTree;
    }

    // Call the visitor to continue the search.
    current->accept(this);

    // Future runs should ocntinue wherever we left off.
    mIsPreviousRun = true;

    // The visitor will set its own "output" in mCurrentPC.
    // This function returns whether we reached the end of the iteration or not.
    return mFoundTarget;

}

/**
 *  Returns the target node's PC.
 *  Only valid after a call to chooseNextTarget() which returned true.
 */
PathCondition DepthFirstSearch::getTargetPC()
{
    return mCurrentPC;
}

void DepthFirstSearch::setDepthLimit(unsigned int depth)
{
    mDepthLimit = depth;
}

unsigned int DepthFirstSearch::getDepthLimit()
{
    return mDepthLimit;
}

// Reset the search to the beginning of the tree.
void DepthFirstSearch::restartSearch()
{
    mIsPreviousRun = false;
    mParentStack.clear();
    mCurrentDepth = 0;
    mCurrentPC = PathCondition();
}





// The visitor part of this class preforms the actual searching.
// Note at any point where the search stops (i.e. there is no call to accept(this) or continueFromLeaf()) then
// we MUST set mFoundTarget appropriately! (This includes in the body of continueFromLeaf().)

void DepthFirstSearch::visit(TraceNode *node)
{
    Log::fatal("Error: Reached a node of unknown type while searching the tree (DFS).");
    exit(1); // TODO: is this appropriate?
}

void DepthFirstSearch::visit(TraceConcreteBranch *node)
{
    // At a branch, we explore only the 'false' subtree.
    // Once we reach a leaf, the parent stack is used to return to branches and explore their 'true' children (see continueFromLeaf()).
    // This allows us to stop the search once we find a node we would like to explore.
    // The depth limit is also enforced here.
    if(mCurrentDepth < mDepthLimit){
        mParentStack.push(SavedPosition(node, mCurrentDepth, mCurrentPC));
        mCurrentDepth++;
        mPreviousParent = node;
        node->getFalseBranch()->accept(this);
        // TODO: do we want to record in mCurrentPC that we went throug a brnach we could not analyse?
        // e.g. add in some NONDET or CONST constraint or something. Would this be any use?
    }else{
        // If we have reached the depth limit, then treat this node as a leaf and skip to whatever we are supposed to search next.
        continueFromLeaf();
    }
}

void DepthFirstSearch::visit(TraceSymbolicBranch *node)
{
    // See TraceConcreteBranch above.
    if(mCurrentDepth < mDepthLimit){
        mParentStack.push(SavedPosition(node, mCurrentDepth, mCurrentPC));
        mCurrentDepth++;
        mPreviousParent = node;
        mCurrentPC.addCondition(node->getSymbolicCondition(), false); // We are always taking the false branch here.
        node->getFalseBranch()->accept(this);
    }else{
        continueFromLeaf();
    }
}

void DepthFirstSearch::visit(TraceUnexplored *node)
{
    // When we reach an unexplored node, we want to return it.
    // Stop the visitor. The PC to return is in mCurrentPC.
    mFoundTarget = true;
}

void DepthFirstSearch::visit(TraceAnnotation *node)
{
    // Skip all annotations, which are only relevant to classification and not searching.
    node->next->accept(this);
}

void DepthFirstSearch::visit(TraceEnd *node)
{
    // When reaching a leaf, we just continue the search and ignore it.
    continueFromLeaf();
}


// When at a leaf node, we can use the parent stack to find the next node to explore.
void DepthFirstSearch::continueFromLeaf()
{
    // Simply pop from the parent stack and take the 'true' branch from there (see visit(TraceBranch*)).
    // If the parent stack is empty, then we are finished.
    if(mParentStack.empty()){
        mFoundTarget = false;
    }else{
        nextAfterLeaf()->accept(this);
    }
}

// From a leaf node, does any bookwork required to move to the next node to explore and returns that node.
// It reminas for the caller to call accept() on the branch this function returns.
// PRECONDITION: Parent stack is non-empty.
TraceNodePtr DepthFirstSearch::nextAfterLeaf()
{
    assert(!mParentStack.empty());

    SavedPosition parent = mParentStack.pop();
    mCurrentDepth = parent.depth;
    mCurrentPC = parent.condition;

    // If the branch is symbolic, we need to add its condition to the current PC.
    TraceSymbolicBranch* sym = dynamic_cast<TraceSymbolicBranch*>(parent.node);
    if(sym){
        mCurrentPC.addCondition(sym->getSymbolicCondition(), true); // We are always taking the true branch here.
    }

    return parent.node->getTrueBranch();
}





} // namespace artemis
