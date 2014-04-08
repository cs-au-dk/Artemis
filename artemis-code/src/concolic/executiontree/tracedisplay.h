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


#include "concolic/executiontree/tracenodes.h"
#include "concolic/traceeventdetectors.h"
#include "concolic/solver/expressionvalueprinter.h"

#include <QString>
#include <QList>
#include <QDateTime>


#ifndef TRACEDISPLAY_H
#define TRACEDISPLAY_H

namespace artemis
{


/**
 * Converts a trace or tree to GraphViz dot format, which can then be
 * output for rendering with GraphViz.
 *
 * TODO: What is a sensible name for this class?
 */
class TraceDisplay : public TraceVisitor
{
public:
    TraceDisplay();
    TraceDisplay(bool simplified);
    TraceDisplay(bool simplified, bool linkToCoverage);

    // The function which is called to generate the output.
    QString makeGraph(TraceNodePtr tree);
    void writeGraphFile(TraceNodePtr tree, QString &pathToFile);
    void writeGraphFile(TraceNodePtr tree, QString &pathToFile, bool autoName);

    // The visitor methods over traces.
    // TODO: we could clean up this interface by putting these into an inner class.
    void visit(TraceNode* node); // Never called unless node types change.
    void visit(TraceConcreteBranch *node);
    void visit(TraceSymbolicBranch *node);
    void visit(TraceUnexplored* node);
    void visit(TraceUnexploredUnsat* node);
    void visit(TraceUnexploredUnsolvable* node);
    void visit(TraceUnexploredMissed* node);
    void visit(TraceAlert* node);
    void visit(TraceDomModification* node);
    void visit(TracePageLoad* node);
    void visit(TraceMarker* node);
    void visit(TraceFunctionCall* node);
    void visit(TraceEndSuccess* node);
    void visit(TraceEndFailure* node);
    void visit(TraceEndUnknown* node);

protected:
    // These lists contain the declarations of nodes which are to be put at the beginning of the file.
    // They include the node labels and any node-specific formatting.
    // Each type (e.g. branches) becomes a subgraph in the result which are styled separately.
    QList<QString> mHeaderBranches, mHeaderSymBranches, mHeaderUnexplored, mHeaderUnexploredUnsat, mHeaderUnexploredUnsolvable, mHeaderUnexploredMissed, mHeaderAlerts, mHeaderDomMods, mHeaderLoads, mHeaderFunctions, mHeaderEndUnk, mHeaderEndSucc, mHeaderEndFail, mHeaderAggregates;
    QMultiMap<QString, QString> mHeaderMarkers;

    // These strings contain the arguments passed to the subgraphs representing each node type.
    // They hold the styling information for each node type.
    QString mStyleBranches, mStyleSymBranches, mStyleUnexplored, mStyleUnexploredUnsat, mStyleUnexploredUnsolvable, mStyleUnexploredMissed, mStyleAlerts, mStyleDomMods, mStyleLoads, mStyleMarkers, mStyleFunctions, mStyleEndUnk, mStyleEndSucc, mStyleEndFail, mStyleAggregates;

    // The edges to be added to the graph.
    QList<QString> mEdges;

    // Stores the previously visited node name (used for generating edges).
    QString mPreviousNode;
    // Any annotations needed when generating the edge.
    QString mEdgeExtras;

    // Used to give unique names to every node.
    int mNodeCounter;

    // The indent used when generating the output file.
    static QString indent;

    // Helpers
    void clearData();
    void addInEdge(QString endpoint);

    // Used to print any symbolic constraints.
    QSharedPointer<ExpressionPrinter> mExpressionPrinter;

    // End success and failure markers do contain a next pointer which shows what part of the tree was "cut off" when inserting them.
    // This parameter controls whether these ignored parts should be shown on the tree or not.
    // For now the parameter is just a constant.
    static bool mPassThroughEndMarkers;

    // There is the option to generate a simplified version of the graph.
    // This will aggregate many "irrelevant" nodes together to make the displayed output much smaller.
    bool mSimplified;

    // The aggregated data which is omitted from the simplified view.
    int mAggregatedConcreteBranches;
    int mAggregatedFunctionCalls;

    // Whether or not we are currently in a "concrete execution phase".
    bool mCurrentlyAggregating;

    // Used to add the aggregated node to the trace.
    void flushAggregation();

    // The legend of the graph, if any.
    QString mLegend;

    // Enable links to a coverage.html file
    bool mLinkToCoverage;
};


} // namespace artemis

#endif // TRACEDISPLAY_H
