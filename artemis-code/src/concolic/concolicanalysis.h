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

#include <QSharedPointer>

#include "runtime/options.h"

#include "concolic/executiontree/tracenodes.h"
#include "concolic/executiontree/tracemerger.h"
#include "concolic/search/explorationdescriptor.h"
#include "concolic/search/search.h"
#include "concolic/search/abstractselector.h"
#include "concolic/solver/solver.h"

#ifndef CONCOLICANALYSIS_H
#define CONCOLICANALYSIS_H

namespace artemis
{

/**
 * ConcolicAnalysis
 *
 * This class provides the top-level controller loop of concolic analysis.
 *
 * Inputs: New symbolic execution traces recorded by the runtime.
 * Outputs: Suggestions for new values to be used in subsequent runs to explore new branches.
 *
 * Note that a return of "nothing left to explore" is not a final verdict if there are still explorations which have
 * been suggested by this class but not yet run and added into the tree.
 *
 * The analysis is performed on traces of a given event sequence. To analyse different event sequences, multiple
 * instances of ConcolicAnalysis must be used.
 */


class ConcolicAnalysis : public QObject
{
    Q_OBJECT

public:
    // TODO: ExplorationHandle was intended to be opaque. Maybe it could be made protected if we only ever passed out pointers instead of actual objects.
    struct ExplorationHandle
    {
        bool noExplorationTarget;
        ExplorationDescriptor target;

        uint explorationIndex;

        ExplorationHandle()
            : noExplorationTarget(false)
            , target()
            , explorationIndex(0)
        {}

        // Hash and equality operators so it can be put into sets, etc.
        friend inline bool operator==(const ExplorationHandle& a, const ExplorationHandle& b)
        {
            return a.noExplorationTarget == b.noExplorationTarget && a.target == b.target ;
        }

        friend inline uint qHash(const ExplorationHandle& key)
        {
            return ::qHash((int)key.noExplorationTarget) ^
                    ::qHash(key.explorationIndex) ^
                    ::qHash(key.target.branch) ^
                    ::qHash((int)key.target.branchDirection);
            // TODO: Why can't I just call ::qHash(key.target) directly? (Compiler complains...)
        }
    };

    enum OutputMode {
        QUIET, CONCOLIC_RUNTIME
    };

    struct ExplorationResult
    {
        // newExploration is false if there is nothing left to explore.
        bool newExploration;

        PathConditionPtr pc;

        // Must be a valid pointer with solution->isSolved() being true if newExploration is true.
        SolutionPtr solution;

        // Opaque handle to be passed back to addTrace() when this result is executed as a new trace.
        ExplorationHandle target;

        // Logging and output stuff
        QString constraintID;
    };



    ConcolicAnalysis(Options options, OutputMode output);

    void addTrace(TraceNodePtr trace, ExplorationHandle target);

    ExplorationResult nextExploration();



    // An ExplorationHandle representing that the exploration did not use values from ConcolicAnalysis.
    // e.g. the very first trace recorded should pass this value to addTrace.
    static const ExplorationHandle NO_EXPLORATION_TARGET;

    // Sets the 'base' DOM restrictions to be used by the analysis.
    // Dynamic restrictions are merged with these based on information from the execution tree.
    // Updating this once the analysis has started will lead to inconsistent results between different traces.
    void setFormRestrictions(FormRestrictions restrictions);

    // Used to enable DOM constraints in the output.
    // If this is set, the pointed-to DomSnapshotStorage should be updated by WebkitExecutor to contain up-to-date snapshots.
    void setDomSnapshotStorage(DomSnapshotStoragePtr domSnapshotStorage);

    // Accessor for the search tree, which should not be externally modified!
    TraceNodePtr getExecutionTree();
    uint getExplorationIndex();


signals:
    void sigExecutionTreeUpdated(TraceNodePtr tree);

protected:

    Options mOptions;
    OutputMode mOutput;

    TraceNodePtr mExecutionTree;

    TraceMerger mTraceMerger;
    TreeSearchPtr mSearchStrategy;

    FormRestrictions mFormFieldInitialRestrictions;
    FormRestrictions mergeDynamicSelectRestrictions(FormRestrictions base, QSet<SelectRestriction> replacements);
    FormRestrictions updateFormRestrictionsForFeatureFlags(FormRestrictions restrictions);

    DomSnapshotStoragePtr mDomSnapshotStorage;

    // Logging
    uint mExplorationIndex;
    QString mPreviousConstraintID;

    // Helpers for addTrace
    void initSearchProcedure();
    void mergeTraceIntoTree(TraceNodePtr trace, ExplorationHandle target);
    AbstractSelectorPtr buildSelector(ConcolicSearchSelector description);

    // Helpers for nextExploration
    SolutionPtr solveTargetPC();
    void printPCInfo(PathConditionPtr pc);
    void handleEmptyPC(ExplorationDescriptor target);

    static ExplorationHandle noExplorationTarget();

    static ExplorationResult nothingToExplore();

    void concolicRuntimeInfo(QString message);
    void concolicRuntimeDebug(QString message);

};

typedef QSharedPointer<ConcolicAnalysis> ConcolicAnalysisPtr;










} // namespace artemis
#endif // CONCOLICANALYSIS_H
