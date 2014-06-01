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

#include "searchdfs.h"
#include "util/loggingutil.h"
#include <assert.h>

namespace artemis
{



DepthFirstSearch::DepthFirstSearch(TraceNodePtr tree, unsigned int depthLimit, unsigned int restartLimit) :
    mTree(tree),
    mDepthLimit(depthLimit),
    mInitialDepthLimit(depthLimit),
    mCurrentDepth(0),
    mRestartsRemaining(restartLimit),
    mUnlimitedRestarts(restartLimit == 0),
    mPreviousPassFoundTarget(false),
    mIsPreviousRun(false)
{
    mCurrentPC = PathConditionPtr(new PathCondition());
    mCurrentDomConstraints = QSet<SelectRestriction>();
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
            // If the parent stack is empty here, then we have reached the end of the search.
            if(mParentStack.empty()){
                mFoundTarget = false;
                return deepenRestartAndChoose();
            }else{
                current = nextAfterLeaf();
            }
        }

    }else{
        // Strat a new search.
        current = mTree;
    }

    // Call the visitor to continue the search.
    current->accept(this);

    // Future runs should continue wherever we left off.
    mIsPreviousRun = true;

    // The visitor will set its own "output" in mCurrentPC.
    // This function returns whether we reached the end of the iteration or not.
    if(mFoundTarget) {
        mPreviousPassFoundTarget = true;
        return true;
    } else {
        // Attempt to increase the depth limit and restart, if possible.
        return deepenRestartAndChoose();
    }

}

/**
 *  Returns the target node's PC.
 *  Only valid after a call to chooseNextTarget() which returned true.
 */
PathConditionPtr DepthFirstSearch::getTargetPC()
{
    return mCurrentPC;
}

QSet<SelectRestriction> DepthFirstSearch::getTargetDomConstraints()
{
    return mCurrentDomConstraints;
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
    mPreviousPassFoundTarget = false;
    mCurrentPC = PathConditionPtr(new PathCondition());
    mCurrentDomConstraints = QSet<SelectRestriction>();
}

// Increase the depth limit and restart.
bool DepthFirstSearch::deepenRestartAndChoose()
{
    if (mPreviousPassFoundTarget && (mUnlimitedRestarts || mRestartsRemaining > 1)) {
        if (!mUnlimitedRestarts){
            mRestartsRemaining --;
        }
        Log::debug("\n============= Finished Search ==============");
        Log::info("Finished this pass of the tree. Increasing depth limit and restarting.");
        setDepthLimit(getDepthLimit() + mInitialDepthLimit);
        restartSearch();
        return chooseNextTarget();
    } else {
       return false;
    }
}





// The visitor part of this class preforms the actual searching.
// Note at any point where the search stops (i.e. there is no call to accept(this) or continueFromLeaf()) then
// we MUST set mFoundTarget appropriately! (This includes in the body of continueFromLeaf().)

void DepthFirstSearch::visit(TraceNode *node)
{
    Log::fatal("Error: Reached a node of unknown type while searching the tree (DFS).");
    exit(1);
}

void DepthFirstSearch::visit(TraceConcreteBranch *node)
{
    // Concrete branches are basically ignored by this search.
    // If there are unexplored nodes as children of a concrete branch, then we ignore them and only search through children of symbolic branches.

    if(isImmediatelyUnexplored(node->getFalseBranch()) && isImmediatelyUnexplored(node->getTrueBranch())){
        Log::fatal("Reached a branch where both branches are unexplored during search.");
        exit(1);

    }else if(isImmediatelyUnexplored(node->getFalseBranch())){
        // Then we treat this node as a pass-through to the 'true' subtree
        node->getTrueBranch()->accept(this);

    }else if(isImmediatelyUnexplored(node->getTrueBranch())){
        // Then we treat this node as a pass-through to the 'false' subtree
        node->getFalseBranch()->accept(this);

    }else{
        // Both branches are explored, so we must search each in turn.
        mParentStack.push(SavedPosition(node, mCurrentDepth, *mCurrentPC, mCurrentDomConstraints));
        //mCurrentDepth++; // Do not increase depth for concrete branches.
        mPreviousParent = node;
        mPreviousDirection = false; // We are always taking the false branch to begin with.
        node->getFalseBranch()->accept(this);
    }
}

void DepthFirstSearch::visit(TraceSymbolicBranch *node)
{
    // At a branch, we explore only the 'false' subtree.
    // Once we reach a leaf, the parent stack is used to return to branches and explore their 'true' children (see continueFromLeaf()).
    // This allows us to stop the search once we find a node we would like to explore.
    // The depth limit is also enforced here.
    if(mCurrentDepth < mDepthLimit){
        mParentStack.push(SavedPosition(node, mCurrentDepth, *mCurrentPC, mCurrentDomConstraints));
        mCurrentDepth++;
        mPreviousParent = node;
        mPreviousDirection = false;
        mCurrentPC->addCondition(node->getSymbolicCondition(), false); // We are always taking the false branch here.
        node->getFalseBranch()->accept(this);
    }else{
        continueFromLeaf();
    }
}

void DepthFirstSearch::visit(TraceConcreteSummarisation *node)
{
    // If this node has only one execution path then it is just an annotation and we pass over it.
    if(node->executions.length() == 1) {
        node->executions[0].second->accept(this);
        return;
    }

    // If there are multiple children, we must add this node to the parent stack so we can explore the rest.
    // The depth limit is ignored for concrete branches.
    if(node->executions.length() > 1) {
        mParentStack.push(SavedPosition(node, mCurrentDepth, *mCurrentPC, mCurrentDomConstraints, 1));
        node->executions[0].second->accept(this);
        // N.B. we do not update mPreviousParent or mPreviousDirection as these should not be used to refer to a
        // concrete summarisation. They are used when we find an unexplored node and attempt to explore it and then
        // need to work out where it used to be in the tree to see if we replaced it or not. Seeing as there must be a
        // true branch node after a concrete summary before we can see an unexplored node these are not necessary here.

    }
}

void DepthFirstSearch::visit(TraceMarker *node)
{
    // Markers may optionally contain some DOM constraints which need to be recorded.
    if(node->isSelectRestriction) {
        mCurrentDomConstraints.insert(node->selectRestriction);
    }
    node->next->accept(this);
}

void DepthFirstSearch::visit(TraceUnexplored *node)
{
    // When we reach an unexplored node, we want to return it.
    // Stop the visitor. The PC to return is in mCurrentPC.
    mFoundTarget = true;
}

void DepthFirstSearch::visit(TraceUnexploredMissed *node)
{
    // For now we will not re-try the same path again (as we don't have any way to generate a different injection).
    continueFromLeaf();
}

void DepthFirstSearch::visit(TraceUnexploredUnsat *node)
{
    // For now we will not re-try the same path again (as we don't have any way to generate a different injection).
    continueFromLeaf();
}

void DepthFirstSearch::visit(TraceUnexploredUnsolvable *node)
{
    // For now we will not re-try the same path again (as we don't have any way to generate a different injection).
    continueFromLeaf();
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
    *mCurrentPC = parent.condition;
    mCurrentDomConstraints = parent.domConstraints;

    // The saved position can either be a branch node or a summary node (with multiple children).
    if(parent.node != NULL) {

        // If the branch is symbolic, we need to add its condition to the current PC.
        // Also update the depth, as we would have done in DepthFirstSearch::visit(TraceSymbolicBranch *node).
        TraceSymbolicBranch* sym = dynamic_cast<TraceSymbolicBranch*>(parent.node);
        if(sym){
            mCurrentPC->addCondition(sym->getSymbolicCondition(), true); // We are always taking the true branch here.
            mCurrentDepth++;
        }

        // Keep the previous parent information up-to-date when branching from the stack.
        mPreviousParent = parent.node;
        mPreviousDirection = true;

        return parent.node->getTrueBranch();

    } else {
        assert(parent.summaryNode != NULL);
        assert(parent.childrenVisited < parent.summaryNode->executions.length());

        // As this branching is concrete, we can leave the PC, depth, etc. as-is.
        // And we also ignore previous parent as in visit(TraceConcreteSummarisation)

        // Push a new entry onto the parent stack to deal with any remaining children, then explore the current one.
        unsigned int currentChild = parent.childrenVisited;
        parent.childrenVisited += 1;

        if(parent.childrenVisited < parent.summaryNode->executions.length()) {
            mParentStack.push(parent);
        }

        return parent.summaryNode->executions[currentChild].second;

    }
}





/*
 *  The functions which deal with marking certain nodes as Unsat, Unsolvable, or Missed.
 *  We do this by replacing the current TraceUnexplored with the relevant marker class.
 */


bool DepthFirstSearch::overUnexploredNode()
{
    // This method can only be called once we have started a search.
    assert(mIsPreviousRun);

    // Use mPreviousParent and mPreviousDirection to find the "current" node again, as in chooseNextTarget().
    TraceNodePtr current;
    if(mPreviousDirection){
        current = mPreviousParent->getTrueBranch();
    }else{
        current = mPreviousParent->getFalseBranch();
    }

    return isImmediatelyUnexplored(current);
}

void DepthFirstSearch::markNodeUnsat()
{
    // This method can only be called once we have started a search.
    assert(mIsPreviousRun);

    // Replace the current node with TraceNodeUnsat.
    if(mPreviousDirection){
        // Replace the true branch of mPreviousParent.
        assert(isImmediatelyUnexplored(mPreviousParent->getTrueBranch()));
        mPreviousParent->setTrueBranch(TraceUnexploredUnsat::getInstance());
    }else{
        // Replace the false branch of mPreviousParent.
        assert(isImmediatelyUnexplored(mPreviousParent->getFalseBranch()));
        mPreviousParent->setFalseBranch(TraceUnexploredUnsat::getInstance());
    }
}

void DepthFirstSearch::markNodeUnsolvable()
{
    // This method can only be called once we have started a search.
    assert(mIsPreviousRun);

    // Replace the current node with TraceUnexploredUnsolvable.
    if(mPreviousDirection){
        // Replace the true branch of mPreviousParent.
        assert(isImmediatelyUnexplored(mPreviousParent->getTrueBranch()));
        mPreviousParent->setTrueBranch(TraceUnexploredUnsolvable::getInstance());
    }else{
        // Replace the false branch of mPreviousParent.
        assert(isImmediatelyUnexplored(mPreviousParent->getFalseBranch()));
        mPreviousParent->setFalseBranch(TraceUnexploredUnsolvable::getInstance());
    }
}

void DepthFirstSearch::markNodeMissed()
{
    // This method can only be called once we have started a search.
    assert(mIsPreviousRun);

    // Replace the current node with TraceUnexploredMissed.
    if(mPreviousDirection){
        // Replace the true branch of mPreviousParent.
        assert(isImmediatelyUnexplored(mPreviousParent->getTrueBranch()));
        mPreviousParent->setTrueBranch(TraceUnexploredMissed::getInstance());
    }else{
        // Replace the false branch of mPreviousParent.
        assert(isImmediatelyUnexplored(mPreviousParent->getFalseBranch()));
        mPreviousParent->setFalseBranch(TraceUnexploredMissed::getInstance());
    }
}





} // namespace artemis
