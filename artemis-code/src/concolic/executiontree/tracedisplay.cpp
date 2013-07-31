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


#include "tracedisplay.h"

#include "util/loggingutil.h"
#include "util/fileutil.h"


namespace artemis
{

QString TraceDisplay::indent = "  ";

TraceDisplay::TraceDisplay()
{
    mExpressionPrinter = QSharedPointer<ExpressionPrinter>(new ExpressionPrinter());
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

    result += indent + "subgraph branches {\n" + indent + indent + "node [label = \"Branch\\n(concrete)\"];\n\n";
    foreach(QString node, mHeaderBranches){
        result += indent + indent + node + ";\n";
    }
    result += indent + "}\n\n";

    result += indent + "subgraph branches_sym {\n";
    foreach(QString node, mHeaderSymBranches){
        result += indent + indent + node + ";\n";
    }
    result += indent + "}\n\n";

    result += indent + "subgraph unexplored {\n" + indent + indent + "node [label = \"???\", shape = circle, style = filled, fillcolor = lightgray];\n\n";
    foreach(QString node, mHeaderUnexplored){
        result += indent + indent + node + ";\n";
    }
    result += indent + "}\n\n";

    result += indent + "subgraph alerts {\n" + indent + indent + "node [shape = rectangle, style = filled, fillcolor = red];\n\n";
    foreach(QString node, mHeaderAlerts){
        result += indent + indent + node + ";\n";
    }
    result += indent + "}\n\n";

    result += indent + "subgraph dom_mods {\n" + indent + indent + "node [label = \"DOM Modification\"];\n\n";
    foreach(QString node, mHeaderDomMods){
        result += indent + indent + node + ";\n";
    }
    result += indent + "}\n\n";

    result += indent + "subgraph loads {\n" + indent + indent + "node [label = \"Page Load\"];\n\n";
    foreach(QString node, mHeaderLoads){
        result += indent + indent + node + ";\n";
    }
    result += indent + "}\n\n";

    result += indent + "subgraph functions {\n" + indent + indent + "node [shape = rectangle];\n\n";
    foreach(QString node, mHeaderFunctions){
        result += indent + indent + node + ";\n";
    }
    result += indent + "}\n\n";

    result += indent + "subgraph end_succ {\n" + indent + indent + "node [label = \"End\", fillcolor = palegreen, style = filled, shape = circle];\n\n";
    foreach(QString node, mHeaderEndSucc){
        result += indent + indent + node + ";\n";
    }
    result += indent + "}\n\n";

    result += indent + "subgraph end_fail {\n" + indent + indent + "node [label = \"End\", fillcolor = tomato, style = filled, shape = circle];\n\n";
    foreach(QString node, mHeaderEndFail){
        result += indent + indent + node + ";\n";
    }
    result += indent + "}\n\n";

    result += indent + "subgraph end_unk {\n" + indent + indent + "node [label = \"End\", fillcolor = lightgray, style = filled, shape = circle];\n\n";
    foreach(QString node, mHeaderEndUnk){
        result += indent + indent + node + ";\n";
    }
    result += indent + "}\n\n";


    // Build the edges list

    result += indent + "start [label = \"Start\"];\n\n";

    foreach(QString edge, mEdges){
        result += indent + edge + ";\n";
    }


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
    QString name = QString("br_%1").arg(mNodeCounter);
    mNodeCounter++;

    mHeaderBranches.append(name);

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
    QString name = QString("sym_%1").arg(mNodeCounter);
    mNodeCounter++;

    node->getSymbolicCondition()->accept(mExpressionPrinter.data());
    QString label = QString(" [label = \"Branch\\n%1\"]").arg(mExpressionPrinter->getResult().c_str());

    // TODO: can we add the symbolic condition to the node label?
    mHeaderSymBranches.append(name + label);

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


void TraceDisplay::visit(TraceUnexplored *node)
{
    QString name = QString("unexp_%1").arg(mNodeCounter);
    mNodeCounter++;

    mHeaderUnexplored.append(name);

    addInEdge(name);
}


void TraceDisplay::visit(TraceAlert *node)
{
    QString name = QString("alt_%1").arg(mNodeCounter);
    mNodeCounter++;

    QString nodeDecl = QString("%1 [label = \"Alert\\n\\\"%2\\\"\"]").arg(name).arg(node->message.left(15));
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

    mHeaderDomMods.append(name);

    addInEdge(name);

    mPreviousNode = name;
    mEdgeExtras = "";
    node->next->accept(this);
}


void TraceDisplay::visit(TracePageLoad *node)
{
    QString name = QString("load_%1").arg(mNodeCounter);
    mNodeCounter++;

    // TODO: Can we add the URL to the node label?
    mHeaderLoads.append(name);

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


void TraceDisplay::visit(TraceEndSuccess *node)
{
    QString name = QString("end_s_%1").arg(mNodeCounter);
    mNodeCounter++;

    mHeaderEndSucc.append(name);

    addInEdge(name);
}


void TraceDisplay::visit(TraceEndFailure *node)
{
    QString name = QString("end_f_%1").arg(mNodeCounter);
    mNodeCounter++;

    mHeaderEndFail.append(name);

    addInEdge(name);
}


void TraceDisplay::visit(TraceEndUnknown *node)
{
    QString name = QString("end_u_%1").arg(mNodeCounter);
    mNodeCounter++;

    mHeaderEndUnk.append(name);

    addInEdge(name);
}





// Clears the member variables contining the items for the header and edges.
void TraceDisplay::clearData()
{
    mHeaderBranches.clear();
    mHeaderUnexplored.clear();
    mHeaderAlerts.clear();
    mHeaderDomMods.clear();
    mHeaderLoads.clear();
    mHeaderFunctions.clear();
    mHeaderEndUnk.clear();
    mHeaderEndSucc.clear();
    mHeaderEndFail.clear();

    mEdges.clear();

    mPreviousNode = "start";
    mEdgeExtras = "";
    mNodeCounter = 0;
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
