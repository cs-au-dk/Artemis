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


#include "tracedisplay.h"

#include <sstream>

#include "util/loggingutil.h"
#include "util/fileutil.h"
#include "model/coverage/coveragelistener.h"


namespace artemis
{

QString TraceDisplay::indent = "  ";

bool TraceDisplay::mPassThroughEndMarkers = false;
bool TraceDisplay::mShowExplorationIndices = true;

TraceDisplay::TraceDisplay()
    : TraceDisplay(false)
{
}

TraceDisplay::TraceDisplay(bool linkToCoverage)
    : mLinkToCoverage(linkToCoverage)
{
    mExpressionPrinter = QSharedPointer<ExpressionPrinter>(new ExpressionValuePrinter());

    mStyleBranches = "[label = \"Branch\\n(concrete)\"]";
    mStyleSymBranches = "[style = filled, fillcolor = azure]";
    mStyleUnexplored = "[label = \"???\", shape = circle, style = filled, fillcolor = lightgray]";
    mStyleUnexploredUnsat = "[label = \"UNSAT\", shape = ellipse, style = filled, fillcolor = blueviolet]";
    mStyleUnexploredUnsolvable = "[label = \"Could not solve\", shape = ellipse, style = filled, fillcolor = hotpink]";
    mStyleUnexploredMissed = "[label = \"Missed\", shape = ellipse, style = filled, fillcolor = chocolate]";
    mStyleUnexploredQueued = "[label = \"Queued\", shape = ellipse, style = filled, fillcolor = white]";
    mStyleAlerts = "[shape = rectangle, style = filled, fillcolor = khaki]";
    mStyleDomMods = "[shape = rectangle, style = filled, fillcolor = peachpuff]";
    mStyleLoads = "[shape = rectangle, style = filled, fillcolor = honeydew]";
    mStyleMarkers = "[shape = rectangle, style = filled, fillcolor = forestgreen]";
    mStyleFunctions = "[shape = rectangle]";
    mStyleEndSucc = "[label = \"Succ\", fillcolor = green, style = filled, shape = circle]";
    mStyleEndFail = "[label = \"Fail\", fillcolor = red, style = filled, shape = circle]";
    mStyleEndUnk = "[label = \"Unk\", fillcolor = yellow, style = filled, shape = circle]";
    mStyleAggregates = "[style = filled, fillcolor = snow, shape = box3d]";

}

/**
 *  Returns a string representing a graphviz input file displaying the trace tree provided.
 */
QString TraceDisplay::makeGraph(TraceNodePtr tree)
{
    QString result;
    /* The visitor part builds up the lists of information which must be included in the "header" and allthe edges
     * in the graph. Then we build this into a actual graphviz file. */

    // Visitor populates mHeader* and mEdges.
    clearData();
    tree->accept(this);

    // Begin the graph
    result += "digraph tree1 {\n" + indent + "graph [ordering = out];\n\n";


    // Build the header (this is where the styling for each node type is done).

    result += indent + "subgraph branches {\n" + indent + indent + "node " + mStyleBranches + ";\n\n";
    foreach(QString node, mHeaderBranches){
        result += indent + indent + node + ";\n";
    }
    result += indent + "}\n\n";

    result += indent + "subgraph branches_sym {\n" + indent + indent + "node " + mStyleSymBranches + ";\n\n";
    foreach(QString node, mHeaderSymBranches){
        result += indent + indent + node + ";\n";
    }
    result += indent + "}\n\n";

    result += indent + "subgraph unexplored {\n" + indent + indent + "node " + mStyleUnexplored + ";\n\n";
    foreach(QString node, mHeaderUnexplored){
        result += indent + indent + node + ";\n";
    }
    result += indent + "}\n\n";

    result += indent + "subgraph unexplored_unsat {\n" + indent + indent + "node " + mStyleUnexploredUnsat + ";\n\n";
    foreach(QString node, mHeaderUnexploredUnsat){
        result += indent + indent + node + ";\n";
    }
    result += indent + "}\n\n";

    result += indent + "subgraph unexplored_unsolvable {\n" + indent + indent + "node " + mStyleUnexploredUnsolvable + ";\n\n";
    foreach(QString node, mHeaderUnexploredUnsolvable){
        result += indent + indent + node + ";\n";
    }
    result += indent + "}\n\n";

    result += indent + "subgraph unexplored_missed {\n" + indent + indent + "node " + mStyleUnexploredMissed + ";\n\n";
    foreach(QString node, mHeaderUnexploredMissed){
        result += indent + indent + node + ";\n";
    }
    result += indent + "}\n\n";

    result += indent + "subgraph unexplored_queued {\n" + indent + indent + "node " + mStyleUnexploredQueued + ";\n\n";
    foreach(QString node, mHeaderUnexploredQueued){
        result += indent + indent + node + ";\n";
    }
    result += indent + "}\n\n";

    result += indent + "subgraph alerts {\n" + indent + indent + "node " + mStyleAlerts + ";\n\n";
    foreach(QString node, mHeaderAlerts){
        result += indent + indent + node + ";\n";
    }
    result += indent + "}\n\n";

    result += indent + "subgraph dom_mods {\n" + indent + indent + "node " + mStyleDomMods + ";\n\n";
    foreach(QString node, mHeaderDomMods){
        result += indent + indent + node + ";\n";
    }
    result += indent + "}\n\n";

    result += indent + "subgraph loads {\n" + indent + indent + "node " + mStyleLoads + ";\n\n";
    foreach(QString node, mHeaderLoads){
        result += indent + indent + node + ";\n";
    }
    result += indent + "}\n\n";

    result += indent + "subgraph markers {\n" + indent + indent + "node " + mStyleMarkers + ";\n\n";
    foreach(QString idx, mHeaderMarkers.uniqueKeys()){
        result += indent + indent + "{\n";
        result += indent + indent + indent + "rank = same;\n";
        result += indent + indent + indent + QString("node [label = \"%1\"];\n").arg(idx);

        foreach(QString node, mHeaderMarkers.values(idx)) {
            result += indent + indent + indent + node + ";\n";
        }

        result += indent + indent + "}\n\n";
    }
    result += indent + "}\n\n";

    result += indent + "subgraph functions {\n" + indent + indent + "node " + mStyleFunctions + ";\n\n";
    foreach(QString node, mHeaderFunctions){
        result += indent + indent + node + ";\n";
    }
    result += indent + "}\n\n";

    result += indent + "subgraph end_succ {\n" + indent + indent + "node " + mStyleEndSucc + ";\n\n";
    foreach(QString node, mHeaderEndSucc){
        result += indent + indent + node + ";\n";
    }
    result += indent + "}\n\n";

    result += indent + "subgraph end_fail {\n" + indent + indent + "node " + mStyleEndFail + ";\n\n";
    foreach(QString node, mHeaderEndFail){
        result += indent + indent + node + ";\n";
    }
    result += indent + "}\n\n";

    result += indent + "subgraph end_unk {\n" + indent + indent + "node " + mStyleEndUnk + ";\n\n";
    foreach(QString node, mHeaderEndUnk){
        result += indent + indent + node + ";\n";
    }
    result += indent + "}\n\n";

    result += indent + "subgraph aggregates {\n" + indent + indent + "node " + mStyleAggregates + ";\n\n";
    foreach(QString node, mHeaderAggregates){
        result += indent + indent + node + ";\n";
    }
    result += indent + "}\n\n";


    // Build the edges list

    result += indent + "start [label = \"Start\"];\n\n";

    foreach(QString edge, mEdges){
        result += indent + edge + ";\n";
    }


    // Add the legend (if any) on the end.
    result += mLegend;


    // End the graph
    result += "\n}\n";


    return result;
}


// Writes the result of makeGraph() to a file.
void TraceDisplay::writeGraphFile(TraceNodePtr tree, QString& pathToFile)
{
    writeGraphFile(tree, pathToFile, true);
}

// Writes the result of makeGraph() to a file.
void TraceDisplay::writeGraphFile(TraceNodePtr tree, QString& pathToFile, bool autoName)
{
    QString data = makeGraph(tree);

    // If autoName is true, we generate a name and "return" it through pathToFile.
    // Otherwise, we use the value given in pathToFile as the name.
    if(autoName){
        pathToFile = QString("graph-%1.gv").arg(QDateTime::currentDateTime().toString("dd-MM-yy-hh-mm-ss"));
    }
    writeStringToFile(pathToFile, data);
}


/*
 *  The node visitor methods.
 *
 *  Each of these must compute its name, add this to the corresponding header list,
 *  add the incoming edge to the edges list, and if there are any children then set
 *  mPreviousNode and mEdgeExtras and then process them.
 */

void TraceDisplay::visit(TraceNode *node)
{
    // Should never be reached.
    Log::fatal("Trace displayer visited a node of unknown type.");
    exit(1);
}


void TraceDisplay::visit(TraceConcreteBranch *node)
{
    mNodeCounter++;

    std::stringstream sourceId;
    sourceId << SourceInfo::getId(node->getSource()->getUrl(), node->getSource()->getStartLine());

    std::stringstream sourceLine;
    sourceLine << node->getLinenumber();

    QString source = "#";
    if (mLinkToCoverage) {
        source = QString("coverage.html?code=ID%1&amp;line=%2").arg(
                    QString::fromStdString(sourceId.str()),
                    QString::fromStdString(sourceLine.str()));
    }

    QString name = QString("br_%1").arg(mNodeCounter);
    QString label = QString(" [URL = \"%1\"]").arg(source);

    mHeaderBranches.append(name + label);

    addInEdge(name);

    // Childeren are displayed in the tree in the order they are specified in the edges list.
    // We want false branches on the left, so process those first.

    mPreviousNode = name;
    mEdgeExtras = "[color = red]";
    node->getFalseBranch()->accept(this);

    mPreviousNode = name;
    mEdgeExtras = "[color = darkgreen]";
    node->getTrueBranch()->accept(this);
}


void TraceDisplay::visit(TraceSymbolicBranch *node)
{
    mNodeCounter++;

    node->getSymbolicCondition()->accept(mExpressionPrinter.data());
    QString symbolicExpression(mExpressionPrinter->getResult().c_str());
    mExpressionPrinter->clear();

    symbolicExpression.replace("\\", "\\\\");
    symbolicExpression.replace("\"", "\\\"");

    std::stringstream sourceId;
    sourceId << SourceInfo::getId(node->getSource()->getUrl(), node->getSource()->getStartLine());

    std::stringstream sourceLine;
    sourceLine << node->getLinenumber();

    QString source = "#";
    if (mLinkToCoverage) {
        source = QString("coverage.html?code=ID%1&amp;line=%2").arg(
                    QString::fromStdString(sourceId.str()),
                    QString::fromStdString(sourceLine.str()));
    }

    QString difficult = "";
    if(node->isDifficult()) {
        difficult = "fillcolor = blue, ";
    }

    QString name = QString("sym_%1").arg(mNodeCounter);
    QString label = QString(" [%1label = \"Branch\\n%2\", URL = \"%3\"]").arg(difficult, symbolicExpression, source);

    mHeaderSymBranches.append(name + label);

    addInEdge(name);

    // Childeren are displayed in the tree in the order they are specified in the edges list.
    // We want false branches on the left, so process those first.

    if(mShowExplorationIndices && node->getExplorationIndex() > 0 && node->getExplorationDirection() == false) {
        mEdgeExtras = QString("[color = red, xlabel = \"%1\"]").arg(node->getExplorationIndex());
    } else {
        mEdgeExtras = "[color = red]";
    }
    mPreviousNode = name;
    node->getFalseBranch()->accept(this);

    if(mShowExplorationIndices && node->getExplorationIndex() > 0 && node->getExplorationDirection() == true) {
        mEdgeExtras = QString("[color = darkgreen, xlabel = \"%1\"]").arg(node->getExplorationIndex());
    } else {
        mEdgeExtras = "[color = darkgreen]";
    }
    mPreviousNode = name;
    node->getTrueBranch()->accept(this);
}


void TraceDisplay::visit(TraceUnexplored *node)
{
    QString name = QString("unexp_%1").arg(mNodeCounter);
    mNodeCounter++;

    mHeaderUnexplored.append(name);

    addInEdge(name);
}

void TraceDisplay::visit(TraceUnexploredUnsat *node)
{
    QString name = QString("unexp_unsat_%1").arg(mNodeCounter);
    mNodeCounter++;

    mHeaderUnexploredUnsat.append(name);

    addInEdge(name);
}

void TraceDisplay::visit(TraceUnexploredUnsolvable *node)
{
    QString name = QString("unexp_unsolvable_%1").arg(mNodeCounter);
    mNodeCounter++;

    mHeaderUnexploredUnsolvable.append(name);

    addInEdge(name);
}

void TraceDisplay::visit(TraceUnexploredMissed *node)
{
    QString name = QString("unexp_missed_%1").arg(mNodeCounter);
    mNodeCounter++;

    mHeaderUnexploredMissed.append(name);

    addInEdge(name);
}

void TraceDisplay::visit(TraceUnexploredQueued *node)
{
    QString name = QString("unexp_queued_%1").arg(mNodeCounter);
    mNodeCounter++;

    mHeaderUnexploredQueued.append(name);

    addInEdge(name);
}


void TraceDisplay::visit(TraceAlert *node)
{
    QString name = QString("alt_%1").arg(mNodeCounter);
    mNodeCounter++;

    QString message = node->message;
    message.replace('\"', "\\\"");
    message.replace('\n', "\\n");
    QString nodeDecl = QString("%1 [label = \"Alert\\n\\\"%2\\\"\"]").arg(name).arg(message);
    mHeaderAlerts.append(nodeDecl);

    addInEdge(name);

    mPreviousNode = name;
    mEdgeExtras = "";
    node->next->accept(this);
}


void TraceDisplay::visit(TraceDomModification *node)
{
    QString name = QString("dom_%1").arg(mNodeCounter);
    mNodeCounter++;

    QString wordList = (node->words.size() > 0 ? "\\nIndicator words:" : "");
    QString word;
    int count;
    foreach(int index, node->words.keys()){
        word = TraceDomModDetector::indicators.at(index);
        count = node->words.value(index);
        wordList += QString("\\n%1: %2").arg(word).arg(count);
    }

    QString nodeDecl = QString("%1 [label = \"DOM Modified: %2% %3\"]").arg(name).arg(node->amountModified).arg(wordList);
    mHeaderDomMods.append(nodeDecl);

    addInEdge(name);

    mPreviousNode = name;
    mEdgeExtras = "";

    node->next->accept(this);
}


void TraceDisplay::visit(TracePageLoad *node)
{
    QString name = QString("load_%1").arg(mNodeCounter);
    mNodeCounter++;

    QString nodeDecl = QString("%1 [label = \"Page Load:\\n%2\"]").arg(name).arg(node->url.toString());
    mHeaderLoads.append(nodeDecl);

    addInEdge(name);

    mPreviousNode = name;
    mEdgeExtras = "";
    node->next->accept(this);
}


void TraceDisplay::visit(TraceMarker *node)
{
    QString name = QString("marker_%1").arg(mNodeCounter);
    mNodeCounter++;

    QString nodeLabel;
    if(node->index == "B") {
        nodeLabel = node->label;
    } else {
        nodeLabel = node->index + ": " + node->label;
    }

    QString nodeDecl = QString("%1 [label = \"%2\"]").arg(name, nodeLabel);
    mHeaderMarkers.insert(node->index, nodeDecl);

    addInEdge(name);

    mPreviousNode = name;
    mEdgeExtras = "";
    node->next->accept(this);
}


void TraceDisplay::visit(TraceFunctionCall *node)
{
    QString name = QString("fun_%1").arg(mNodeCounter);
    mNodeCounter++;

    QString funcName = node->name.isEmpty() ? "(anonymous)" : (node->name + "()");
    QString nodeDecl = QString("%1 [label = \"%2\"]").arg(name).arg(funcName);
    mHeaderFunctions.append(nodeDecl);

    addInEdge(name);

    mPreviousNode = name;
    mEdgeExtras = "";

    node->next->accept(this);
}


void TraceDisplay::visit(TraceConcreteSummarisation *node)
{
    QString name = QString("aggr_%1").arg(mNodeCounter);
    mNodeCounter++;

    QStringList executionStats;
    QList<int> functions = node->numFunctions();
    QList<int> branches = node->numBranches();
    for(int i = 0; i < node->executions.length(); i++) {
        executionStats.append(QString("\\n Branches: %2  \\n Function Calls: %3  \\n").arg(branches[i]).arg(functions[i]));
    }

    QString nodeDecl = QString("%1 [label = \"\\n Concrete Execution %2 \"]").arg(name).arg(executionStats.join("---"));
    mHeaderAggregates.append(nodeDecl);

    addInEdge(name);

    foreach(TraceConcreteSummarisation::SingleExecution execution, node->executions) {
        mPreviousNode = name;
        mEdgeExtras = "";

        execution.second->accept(this);
    }
}


void TraceDisplay::visit(TraceEndSuccess *node)
{
    QString name = QString("end_s_%1").arg(mNodeCounter);
    mNodeCounter++;

    QStringList indices;
    QList<uint> sorted = node->traceIndices.toList();
    qSort(sorted);
    foreach(uint idx, sorted) {
        indices.append(QString::number(idx));
    }

    QString nodeDecl;
    if(mShowExplorationIndices) {
        nodeDecl = QString("%1 [xlabel = \"%2\"]").arg(name).arg(indices.join(", "));
    } else {
        nodeDecl = name;
    }
    mHeaderEndSucc.append(nodeDecl);

    addInEdge(name);

    if(mPassThroughEndMarkers){
        mPreviousNode = name;
        mEdgeExtras = "";
        node->next->accept(this);
    }
}


void TraceDisplay::visit(TraceEndFailure *node)
{
    QString name = QString("end_f_%1").arg(mNodeCounter);
    mNodeCounter++;

    QStringList indices;
    QList<uint> sorted = node->traceIndices.toList();
    qSort(sorted);
    foreach(uint idx, sorted) {
        indices.append(QString::number(idx));
    }

    QString nodeDecl;
    if(mShowExplorationIndices) {
        nodeDecl = QString("%1 [xlabel = \"%2\"]").arg(name).arg(indices.join(", "));
    } else {
        nodeDecl = name;
    }
    mHeaderEndFail.append(nodeDecl);

    addInEdge(name);

    if(mPassThroughEndMarkers){
        mPreviousNode = name;
        mEdgeExtras = "";
        node->next->accept(this);
    }
}


void TraceDisplay::visit(TraceEndUnknown *node)
{
    QString name = QString("end_u_%1").arg(mNodeCounter);
    mNodeCounter++;

    QStringList indices;
    QList<uint> sorted = node->traceIndices.toList();
    qSort(sorted);
    foreach(uint idx, sorted) {
        indices.append(QString::number(idx));
    }

    QString nodeDecl;
    if(mShowExplorationIndices) {
        nodeDecl = QString("%1 [xlabel = \"%2\"]").arg(name).arg(indices.join(", "));
    } else {
        nodeDecl = name;
    }
    mHeaderEndUnk.append(nodeDecl);

    addInEdge(name);
}





// Clears the member variables contining the items for the header and edges.
void TraceDisplay::clearData()
{
    mHeaderBranches.clear();
    mHeaderSymBranches.clear();
    mHeaderUnexplored.clear();
    mHeaderUnexploredUnsat.clear();
    mHeaderUnexploredUnsolvable.clear();
    mHeaderUnexploredMissed.clear();
    mHeaderUnexploredQueued.clear();
    mHeaderAlerts.clear();
    mHeaderDomMods.clear();
    mHeaderLoads.clear();
    mHeaderMarkers.clear();
    mHeaderFunctions.clear();
    mHeaderEndUnk.clear();
    mHeaderEndSucc.clear();
    mHeaderEndFail.clear();
    mHeaderAggregates.clear();

    mEdges.clear();

    mPreviousNode = "start";
    mEdgeExtras = mShowExplorationIndices ? "[xlabel = \"1\"]" : "";
    mNodeCounter = 0;

    mExpressionPrinter->clear();
}

// Adds a new edge to mEdges.
void TraceDisplay::addInEdge(QString endpoint)
{
    QString edge = QString("%1 -> %2").arg(mPreviousNode).arg(endpoint);
    if(!mEdgeExtras.isEmpty()){
        edge += " " + mEdgeExtras;
    }
    mEdges.append(edge);
}



} //namespace artemis
