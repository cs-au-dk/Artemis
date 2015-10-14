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

#include "concolicanalysis.h"

#include "concolic/search/searchdfs.h"
#include "concolic/search/randomaccesssearch.h"
#include "concolic/search/avoidunsatselector.h"
#include "concolic/search/dfsselector.h"
#include "concolic/search/randomisedselector.h"
#include "concolic/search/roundrobinselector.h"
#include "concolic/executiontree/treemanager.h"
#include "concolic/executiontree/traceindexer.h"

#include <assert.h>

namespace artemis
{

const ConcolicAnalysis::ExplorationHandle ConcolicAnalysis::NO_EXPLORATION_TARGET = ConcolicAnalysis::noExplorationTarget();

ConcolicAnalysis::ConcolicAnalysis(Options options, OutputMode output)
    : mOptions(options)
    , mOutput(output)
    , mExecutionTree(TraceNodePtr())
    , mSearchStrategy(TreeSearchPtr())
    , mDomSnapshotStorage(DomSnapshotStoragePtr(new DomSnapshotStorage()))
    , mExplorationIndex(1)
    , mPreviousConstraintID()
{
}

// Add a new trace to the tree.
void ConcolicAnalysis::addTrace(TraceNodePtr trace, ExplorationHandle target)
{
    // If there is no exploration target we do not know the trace index, unless it is the initial trace.
    // For these "unknown" traces, leave the index blank.
    if (!target.noExplorationTarget || mExecutionTree.isNull()) {
        uint index = target.noExplorationTarget ? 1 : target.explorationIndex;
        TraceIndexer::index(trace, index);
    }

    // If this is the first trace, then we need to intialise the tree and search procedure.
    // We can't just begin with an empty tree and merge every trace in, as the search procedure needs a
    // pointer to the tree, which will be replaced in that case.
    if (mExecutionTree.isNull()) {
        mExecutionTree = trace;
        initSearchProcedure();
    } else {
        mergeTraceIntoTree(trace, target);
    }

    emit sigExecutionTreeUpdated(mExecutionTree, mConcolicAnalysisName);
}

// Initilises mSearchProcedure.
void ConcolicAnalysis::initSearchProcedure()
{
    assert(mSearchStrategy.isNull());

    Statistics::statistics()->accumulate("Concolic::ExecutionTree::DistinctTracesExplored", 1);

    switch(mOptions.concolicSearchProcedure) {
    case SEARCH_DFS:
        mSearchStrategy = TreeSearchPtr(new DepthFirstSearch(mExecutionTree,
                                                             mOptions.concolicDfsDepthLimit,
                                                             mOptions.concolicDfsRestartLimit));
        QObject::connect(&mTraceMerger, SIGNAL(sigTraceJoined(TraceNodePtr, int, TraceNodePtr, TraceNodePtr)),
                         mSearchStrategy.dynamicCast<DepthFirstSearch>().data(), SLOT(slNewTraceAdded(TraceNodePtr, int, TraceNodePtr, TraceNodePtr)));
        break;

    case SEARCH_SELECTOR:
        mSearchStrategy = TreeSearchPtr(new RandomAccessSearch(mExecutionTree,
                                                               buildSelector(mOptions.concolicSearchSelector),
                                                               mOptions.concolicSearchBudget));
        QObject::connect(&mTraceMerger, SIGNAL(sigTraceJoined(TraceNodePtr, int, TraceNodePtr, TraceNodePtr)),
                         mSearchStrategy.dynamicCast<RandomAccessSearch>().data(), SLOT(slNewTraceAdded(TraceNodePtr, int, TraceNodePtr, TraceNodePtr)));
        break;

    default:
        Log::fatal("Unknown search procedure.");
        exit(1);
    }
}

void ConcolicAnalysis::mergeTraceIntoTree(TraceNodePtr trace, ExplorationHandle target)
{
    assert(!mExecutionTree.isNull());

    mExecutionTree = mTraceMerger.merge(trace, mExecutionTree, &mExecutionTree);

    // Check if we actually explored the intended target.
    if (!target.noExplorationTarget && TreeManager::isQueuedOrNotAttempted(target.target)) {
        TreeManager::markNodeMissed(target.target);
        concolicRuntimeInfo("  Recorded trace did not take the expected path.");
    }
}

// Creates the selector used in a RandomAccessSearch search strategy.
AbstractSelectorPtr ConcolicAnalysis::buildSelector(ConcolicSearchSelector description)
{
    AbstractSelectorPtr selector;
    QList<AbstractSelectorPtr> children;

    switch(description.type) {
    case ConcolicSearchSelector::SELECTOR_DFS:
        selector = AbstractSelectorPtr(new DFSSelector());
        break;
    case ConcolicSearchSelector::SELECTOR_RANDOM:
        selector = AbstractSelectorPtr(new RandomisedSelector());
        break;
    case ConcolicSearchSelector::SELECTOR_AVOID_UNSAT:
        selector = AbstractSelectorPtr(new AvoidUnsatSelector());
        break;
    case ConcolicSearchSelector::SELECTOR_ROUND_ROBIN:
        foreach(ConcolicSearchSelector childDescription, description.components) {
            children.append(buildSelector(childDescription));
        }
        selector = AbstractSelectorPtr(new RoundRobinSelector(children));
        break;
    default:
        Log::fatal("ERROR: Unsupported choice of concolic-selection-procedure.");
        exit(1);
    }

    return selector;
}









// Find the next exploration target and return a solution.
ConcolicAnalysis::ExplorationResult ConcolicAnalysis::nextExploration()
{
    ExplorationResult result;
    bool foundResult;
    ExplorationHandle handle;
    SolutionPtr solution;
    PathConditionPtr pc;

    // If the tree is not yet initialised, then return nothing.
    if (mSearchStrategy.isNull()) {
        return nothingToExplore();
    }

    // Search until we find a solution for new exploration
    foundResult = false;
    while (!foundResult) {
        // Call the search procedure to find an unexplored PC.
        if (mSearchStrategy->chooseNextTarget()) {

            mExplorationIndex++;

            handle.noExplorationTarget = false;
            handle.target = mSearchStrategy->getTargetDescriptor();
            handle.explorationIndex = mExplorationIndex;

            pc = mSearchStrategy->getTargetPC();

            solution = solveTargetPC();

            // If the solution is OK we are done. If it's UNSAT, unsolvable, etc. then re-try a new search target.
            if (!solution.isNull() && solution->isSolved()) {
                result.newExploration = true;
                result.pc = pc;
                result.solution = solution;
                result.target = handle;
                result.constraintID = mPreviousConstraintID;

                foundResult = true;
                TreeManager::markNodeQueued(handle.target);
            }

        } else {
            // Search procedure could not find anything new to search.
            result = nothingToExplore();
            foundResult = true;
        }
    }

    // Returns the solved result, or nothingToExplore() if no SAT PC could be found.
    return result;
}


// Runs the solver on the current search target and returns the solution.
// Includes the optimisation to re-try unsolvable constraints with clauses dropped.
SolutionPtr ConcolicAnalysis::solveTargetPC()
{
    PathConditionPtr pc = mSearchStrategy->getTargetPC();
    ExplorationDescriptor target = mSearchStrategy->getTargetDescriptor();
    QSet<SelectRestriction> dynamicSelectConstraints = mSearchStrategy->getTargetDomConstraints();

    printPCInfo(pc);

    // If the returned PC is empty then there are no solvable copnstraints on the path.
    if (pc->size() < 1) {
        handleEmptyPC(target);
        return SolutionPtr();
    }

    // Merge the dynamic DOM constraints (select only for now) with the static "defaults".
    FormRestrictions dynamicRestrictions = mergeDynamicSelectRestrictions(mFormFieldInitialRestrictions, dynamicSelectConstraints);
    dynamicRestrictions = updateFormRestrictionsForFeatureFlags(dynamicRestrictions);

    TreeManager::markExplorationIndex(target, mExplorationIndex);

    // Try to solve this PC to get some concrete input.
    SolverPtr solver = Solver::getSolver(mOptions);
    SolutionPtr solution = solver->solve(pc, dynamicRestrictions, mDomSnapshotStorage);
    mPreviousConstraintID = solver->getLastConstraintID();

    // If the constraint could not be solved, then we have an oppourtunity to retry.
    bool canRetry = true;
    while (!solution->isSolved() && !solution->isUnsat() && canRetry) {

        // Check if there was a specific clause which caused this PC to be unsolvable and mark it as difficult.
        if(solution->getUnsolvableClause() >= 0) {
            TraceSymbolicBranch* difficultBranch = pc->getBranch(solution->getUnsolvableClause());
            assert(!difficultBranch->isDifficult()); // We should never have tried to solve a known difficult branch. Otherwise we may get stuck in a loop when we retry!
            difficultBranch->markDifficult();
            Statistics::statistics()->accumulate("Concolic::ExecutionTree::DifficultBranches", 1);
        }

        // There is nothing we can do in the following cases:
        //    * There was no bad clause identified
        //    * The bad clause was from the node we were directly targeting
        // Otherwise we can re-try writing the PC without this difficult clause.
        if (solution->getUnsolvableClause() < 0 || (uint)solution->getUnsolvableClause() == pc->size()-1) {
            TreeManager::markNodeUnsolvable(target);
            concolicRuntimeInfo("  Could not solve constraint:");
            concolicRuntimeInfo(QString("    %1").arg(solution->getUnsolvableReason()));
            concolicRuntimeDebug("Skipping this target!");

            emit sigExecutionTreeUpdated(mExecutionTree, mConcolicAnalysisName);
            canRetry = false;

        } else {
            concolicRuntimeInfo("  Could not solve this constraint. Re-trying after marking as difficult.");
            Statistics::statistics()->accumulate("Concolic::DifficultBranchRetries", 1);

            // As we have marked the bad node as difficult already, Search::getTargetPC() will return an updated PC.
            pc = mSearchStrategy->getTargetPC();

            printPCInfo(pc);

            // Check for empty PC, in which case we must give up.
            if (pc->size() < 1) {
                handleEmptyPC(target);
                solution = SolutionPtr();
                canRetry = false;
            } else {

                solution = solver->solve(pc, dynamicRestrictions, mDomSnapshotStorage);
                mPreviousConstraintID = solver->getLastConstraintID();

            }

        }
    }

    // Now we have made a "best-effort" to solve the PC, but it could still be either solved, unsat, or unsolvable.

    if (solution->isUnsat()) {
        TreeManager::markNodeUnsat(target);
        concolicRuntimeInfo("  Constraint is UNSAT.");
        concolicRuntimeDebug("Skipping this target!");
        emit sigExecutionTreeUpdated(mExecutionTree, mConcolicAnalysisName);
    }

    return solution;
}

void ConcolicAnalysis::printPCInfo(PathConditionPtr pc)
{
    concolicRuntimeInfo("  Next target:");
    QString targetString = QString("    ") + QString::fromStdString(pc->toStatisticsValuesString(true)).trimmed();
    targetString.replace('\n', "\n    ");
    concolicRuntimeInfo(targetString);

    // Get (and print) the list of free variables in the target PC.
    QMap<QString, Symbolic::SourceIdentifierMethod> injectionVariables = pc->freeVariables();
    QStringList varList = injectionVariables.keys();

    concolicRuntimeDebug(QString("Variables we need to solve (%1):").arg(varList.length()));
    concolicRuntimeDebug(varList.join(", "));
}

void ConcolicAnalysis::handleEmptyPC(ExplorationDescriptor target)
{
    TreeManager::markNodeUnsolvable(target);

    concolicRuntimeInfo("  Could not solve constraint:");
    concolicRuntimeInfo("    All branches on path were known to be difficult.");
    concolicRuntimeDebug("Skipping this target!");

    emit sigExecutionTreeUpdated(mExecutionTree, mConcolicAnalysisName);
}







void ConcolicAnalysis::setFormRestrictions(FormRestrictions restrictions)
{
    mFormFieldInitialRestrictions = restrictions;
}

void ConcolicAnalysis::setDomSnapshotStorage(DomSnapshotStoragePtr domSnapshotStorage)
{
    mDomSnapshotStorage = domSnapshotStorage;
}

TraceNodePtr ConcolicAnalysis::getExecutionTree()
{
    return mExecutionTree;
}

uint ConcolicAnalysis::getExplorationIndex()
{
    return mExplorationIndex;
}

FormRestrictions ConcolicAnalysis::mergeDynamicSelectRestrictions(FormRestrictions base, QSet<SelectRestriction> replacements)
{
    // Copy the radio constraints across as-is, they are not handled dynamically yet.
    // Merge in the updated constraints from the search procedure with the latest "default" ones from base.

    FormRestrictions updated = base;
    updated.first = replacements;

    QSet<QString> replacementVariables;
    foreach(SelectRestriction sr, replacements) {
        concolicRuntimeDebug(QString("We have an updated value for %1").arg(sr.variable));
        replacementVariables.insert(sr.variable);
    }

    foreach(SelectRestriction sr, base.first) {
        if (!replacementVariables.contains(sr.variable)) {
            concolicRuntimeDebug(QString("Using the default value for value for %1").arg(sr.variable));
            updated.first.insert(sr);
        }
    }

    return updated;
}

FormRestrictions ConcolicAnalysis::updateFormRestrictionsForFeatureFlags(FormRestrictions restrictions)
{
    // If these features have been disabled, then remove the restrictions.
    if (mOptions.concolicDisabledFeatures.testFlag(SELECT_RESTRICTION_DYNAMIC)) {
        if (restrictions.first != mFormFieldInitialRestrictions.first) {
            Statistics::statistics()->accumulate("Concolic::Solver::SelectDynamicDomConstraintsIgnored", 1);
        }
        restrictions.first = mFormFieldInitialRestrictions.first;
    }
    if (mOptions.concolicDisabledFeatures.testFlag(SELECT_RESTRICTION)) {
        restrictions.first.clear();
    }
    if (mOptions.concolicDisabledFeatures.testFlag(RADIO_RESTRICTION)) {
        restrictions.second.clear();
    }

    return restrictions;
}

ConcolicAnalysis::ExplorationHandle ConcolicAnalysis::noExplorationTarget()
{
    ExplorationHandle noTarget;
    noTarget.noExplorationTarget = true;
    return noTarget;
}

ConcolicAnalysis::ExplorationResult ConcolicAnalysis::nothingToExplore()
{
    ExplorationResult noExploration;
    noExploration.newExploration = false;
    return noExploration;
}

void ConcolicAnalysis::concolicRuntimeInfo(QString message)
{
    if (mOutput == CONCOLIC_RUNTIME) {
        Log::info(message.toStdString());
    }
}

void ConcolicAnalysis::concolicRuntimeDebug(QString message)
{
    if (mOutput == CONCOLIC_RUNTIME) {
        Log::debug(message.toStdString());
    }
}

void ConcolicAnalysis::setName(QString name)
{
    mConcolicAnalysisName = name;
}

} //namespace artemis
