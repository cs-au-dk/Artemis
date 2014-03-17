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


#include "tracedisplayoverview.h"
#include "util/loggingutil.h"


namespace artemis {

TraceDisplayOverview::TraceDisplayOverview()
    : TraceDisplayOverview(false, false)
{
}

TraceDisplayOverview::TraceDisplayOverview(bool simple)
    : TraceDisplayOverview(simple, false)
{
}

TraceDisplayOverview::TraceDisplayOverview(bool simple, bool linkToCoverage)
    : TraceDisplay(simple, linkToCoverage)
{
    // Override the styles for each node type to make them simpler.

    mStyleBranches = "[label = \"\", shape = circle, style = filled, fillcolor = black]";
    mStyleSymBranches = "[label = \"\", shape = circle, style = filled, fillcolor = cyan]";
    mStyleUnexplored = "[label = \"?\", shape = circle, style = filled, fillcolor = lightgray]";
    mStyleUnexploredUnsat = "[label = \"U\", shape = circle, style = filled, fillcolor = blueviolet]";
    mStyleUnexploredUnsolvable = "[label = \"X\", shape = circle, style = filled, fillcolor = hotpink]";
    mStyleUnexploredMissed = "[label = \"M\", shape = circle, style = filled, fillcolor = chocolate]";
    mStyleAlerts = "[label = \"!\", shape = circle, style = filled, fillcolor = gold]";
    mStyleDomMods = "[label = \"W\", shape = circle, style = filled, fillcolor = peachpuff]";
    mStyleLoads = "[label = \"L\" shape = circle, style=filled, fillcolor = honeydew]";
    //mStyleFunctions not used
    mStyleEndSucc = "[label = \"S\", fillcolor = green, style = filled, shape = circle]";
    mStyleEndFail = "[label = \"F\", fillcolor = red, style = filled, shape = circle]";
    mStyleEndUnk = "[label = \"E\", fillcolor = lightgray, style = filled, shape = circle]";
    //mStyleAggregates not used


    // Add a legend.
    mLegend = "  {\n"
            "    legend_node [shape=none, margin=0, label=<\n"
            "    <table border=\"0\" cellborder=\"0\" cellspacing=\"10pt\" cellpadding=\"5pt\">\n"
            "      <tr><td colspan=\"4\"><b>Legend</b></td></tr>\n"
            "      <tr>\n"
            "        <td bgcolor=\"black\" border=\"1\" width=\"25pt\"></td>\n"
            "        <td align=\"left\">Concrete Branch</td>\n"
            "\n"
            "        <td bgcolor=\"gold\" border=\"1\" width=\"25pt\">!</td>\n"
            "        <td align=\"left\">Alert</td>\n"
            "      </tr>\n"
            "      <tr>\n"
            "        <td bgcolor=\"cyan\" border=\"1\" width=\"25pt\"></td>\n"
            "        <td align=\"left\">Symbolic Branch</td>\n"
            "\n"
            "        <td bgcolor=\"honeydew\" border=\"1\" width=\"25pt\">L</td>\n"
            "        <td align=\"left\">Page Load</td>\n"
            "      </tr>\n"
            "      <tr>\n"
            "        <td bgcolor=\"green\" border=\"1\" width=\"25pt\">S</td>\n"
            "        <td align=\"left\">End (Success)</td>\n"
            "\n"
            "        <td bgcolor=\"peachpuff\" border=\"1\" width=\"25pt\">W</td>\n"
            "        <td align=\"left\">Indicator word added</td>\n"
            "      </tr>\n"
            "      <tr>\n"
            "        <td bgcolor=\"red\" border=\"1\" width=\"25pt\">F</td>\n"
            "        <td align=\"left\">End (Failure)</td>\n"
            "\n"
            "        <td bgcolor=\"blueviolet\" border=\"1\" width=\"25pt\">U</td>\n"
            "        <td align=\"left\">Unsatisfiable</td>\n"
            "      </tr>\n"
            "      <tr>\n"
            "        <td bgcolor=\"lightgray\" border=\"1\" width=\"25pt\">E</td>\n"
            "        <td align=\"left\">End (Unknown)</td>\n"
            "\n"
            "        <td bgcolor=\"chocolate\" border=\"1\" width=\"25pt\">M</td>\n"
            "        <td align=\"left\">Missed</td>\n"
            "      </tr>\n"
            "      <tr>\n"
            "        <td bgcolor=\"lightgray\" border=\"1\" width=\"25pt\">?</td>\n"
            "        <td align=\"left\">Unexplored</td>\n"
            "\n"
            "        <td bgcolor=\"hotpink\" border=\"1\" width=\"25pt\">X</td>\n"
            "        <td align=\"left\">Could not solve</td>\n"
            "      </tr>\n"
            "    </table>\n"
            "    >];\n"
            "  }\n";


}





/*
 *  The node visitor methods.
 *
 *  Each of these must compute its name, add this to the corresponding header list,
 *  add the incoming edge to the edges list, and if there are any children then set
 *  mPreviousNode and mEdgeExtras and then process them.
 *
 *  However, note that in overview mode we will be "skipping" certain nodes.
 */



void TraceDisplayOverview::visit(TraceConcreteBranch *node)
{
    QString name = QString("br_%1").arg(mNodeCounter);
    mNodeCounter++;

    // If both branches are explored, we want to show them. Otherwise they are skipped.
    if(!isImmediatelyUnexplored(node->getFalseBranch()) && !isImmediatelyUnexplored(node->getTrueBranch())){
        // Show the branch.
        mHeaderBranches.append(name);
        addInEdge(name);

        // Process the children (false/left first).
        mPreviousNode = name;
        mEdgeExtras = "[color = red]";
        node->getFalseBranch()->accept(this);

        mPreviousNode = name;
        mEdgeExtras = "[color = darkgreen]";
        node->getTrueBranch()->accept(this);

    }else if(isImmediatelyUnexplored(node->getFalseBranch()) && !isImmediatelyUnexplored(node->getTrueBranch())){
        // Skip this node and continue on true branch.
        node->getTrueBranch()->accept(this);

    }else if(!isImmediatelyUnexplored(node->getFalseBranch()) && isImmediatelyUnexplored(node->getTrueBranch())){
        // Skip this node and continue on false branch.
        node->getFalseBranch()->accept(this);

    }else{
        // No children explored... this is an error.
        Log::warning("Warning: Reached a branch with no children in TraceDisplayOverview.");
    }

}


void TraceDisplayOverview::visit(TraceSymbolicBranch *node)
{
    flushAggregation(); // Not currently used in overview mode.

    QString name = QString("sym_%1").arg(mNodeCounter);
    mNodeCounter++;

    // We always show symbolic brnaches, but we no longer need to find their conditions, etc.

    mHeaderSymBranches.append(name);
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




void TraceDisplayOverview::visit(TraceAlert *node)
{
    flushAggregation();

    QString name = QString("alt_%1").arg(mNodeCounter);
    mNodeCounter++;

    // Always show alerts, but no longer include messages.
    mHeaderAlerts.append(name);
    addInEdge(name);

    mPreviousNode = name;
    mEdgeExtras = "";
    node->next->accept(this);
}


void TraceDisplayOverview::visit(TraceDomModification *node)
{
    if(node->words.size() > 0){
        flushAggregation();

        QString name = QString("dom_%1").arg(mNodeCounter);
        mNodeCounter++;

        mHeaderDomMods.append(name);
        addInEdge(name);

        mPreviousNode = name;
        mEdgeExtras = "";
    }

    node->next->accept(this);
}


void TraceDisplayOverview::visit(TracePageLoad *node)
{
    flushAggregation();

    QString name = QString("load_%1").arg(mNodeCounter);
    mNodeCounter++;

    // Always show loads, but no longer show messages.
    mHeaderLoads.append(name);
    addInEdge(name);

    mPreviousNode = name;
    mEdgeExtras = "";
    node->next->accept(this);
}


void TraceDisplayOverview::visit(TraceFunctionCall *node)
{
    // Skip these nodes.
    node->next->accept(this);
}




} //namespace artemis
