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


#include "traceprinter.h"
#include "util/loggingutil.h"


namespace artemis
{




/* Boring Trace Printer ******************************************************/



void VeryBoringTracePrintingVisitor::visit(TraceNode* node)
{
    Log::info("VBTP: At a NODE.");
}



/* Detailed Trace Printer ****************************************************/



void CompleteTracePrintingVisitor::visit(TraceNode* node)
{
    Log::info("CTPV: At a NODE. THIS SHOULD NEVER BE REACHED!");
}

void CompleteTracePrintingVisitor::visit(TraceBranch* node)
{
    Log::info("CTPV: At a BRANCH.");
}

void CompleteTracePrintingVisitor::visit(TraceUnexplored* node)
{
    Log::info("CTPV: At an UNEXPLORED.");
}

void CompleteTracePrintingVisitor::visit(TraceAlert* node)
{
    Log::info("CTPV: At an ALERT.");
}

void CompleteTracePrintingVisitor::visit(TraceDomModification* node)
{
    Log::info("CTPV: At a DOM CHANGE.");
}

void CompleteTracePrintingVisitor::visit(TracePageLoad* node)
{
    Log::info("CTPV: At a PAGE LOAD.");
}

void CompleteTracePrintingVisitor::visit(TraceEndSuccess* node)
{
    Log::info("CTPV: At an END SUCCESS.");
}

void CompleteTracePrintingVisitor::visit(TraceEndFailure* node)
{
    Log::info("CTPV: At an END FAIL.");
}

void CompleteTracePrintingVisitor::visit(TraceEndUnknown* node)
{
    Log::info("CTPV: At an END UNK.");
}



/* Search-Style Trace Printer ************************************************/





void SearchStylePrintingVisitor::visit(TraceNode* node)
{
    Log::info("SSPV: At a NODE. SHOULD NOT BE REACHABLE.");
}

void SearchStylePrintingVisitor::visit(TraceBranch* node)
{
    Log::info("SSPV: At a BRANCH.");
}

void SearchStylePrintingVisitor::visit(TraceUnexplored* node)
{
    Log::info("SSPV: At an UNEXPLORED.");
}

void SearchStylePrintingVisitor::visit(TraceAnnotation* node)
{
    Log::info("SSPV: At an ANNOTATION (of some kind).");
}

void SearchStylePrintingVisitor::visit(TraceEndSuccess* node)
{
    Log::info("SSPV: At an END SUCCESS.");
}

void SearchStylePrintingVisitor::visit(TraceEndFailure* node)
{
    Log::info("SSPV: At an ENS FAILURE.");
}

void SearchStylePrintingVisitor::visit(TraceEndUnknown* node)
{
    Log::info("SSPV: At an END UNK.");
}



/* Termianl Trace Printer ****************************************************/


TerminalTracePrinter::TerminalTracePrinter()
{
}

void TerminalTracePrinter::printTraceTree(TraceNodePtr root)
{
    // Reset the current state.
    mCurrentTree.clear();
    mCompletedLeftTrees.clear();

    // Run the visitor.
    root->accept(this);

    // Now mCurrentTree should be set to the entire result.
    Log::info("");
    QString leftPadding = " ";
    Log::info((QString(mCurrentTree.connector - 2 + leftPadding.length(), ' ') + "START").toStdString());
    Log::info((QString(mCurrentTree.connector + leftPadding.length(), ' ') + "|").toStdString());
    foreach(QString line, mCurrentTree.lines){
        Log::info((leftPadding + line).toStdString());
    }
    Log::info("");

    // Check there is nothing left in the list of intermediate trees...
    if(!mCompletedLeftTrees.empty()){
        Log::info("ERROR: tree printing did not print the entire tree.");
    }

}


void TerminalTracePrinter::visit(TraceNode* node)
{
    // Should never be reached.
    // There is nowhere we can go from here as general nodes don't have a successor!
    addSingleValue("ERROR");
}

void TerminalTracePrinter::visit(TraceBranch* node)
{
    // First process the left tree.
    node->branchFalse->accept(this);

    // Now mCurrentTree represents the left subtree, so copy it into mCompletedLeftSubtrees.
    mCompletedLeftTrees.push(mCurrentTree);

    // Now clear the current tree and process the right subtree.
    mCurrentTree.clear();
    node->branchTrue->accept(this);

    // Now we have both trees, so join them.
    addBranch("Branch");
}

void TerminalTracePrinter::visit(TraceUnexplored* node)
{
    addSingleValue("???");
}

void TerminalTracePrinter::visit(TraceAlert* node)
{
    node->next->accept(this);
    addSingleValue("Alert");
}

void TerminalTracePrinter::visit(TraceDomModification* node)
{
    node->next->accept(this);
    addSingleValue("DOM");
}

void TerminalTracePrinter::visit(TracePageLoad* node)
{
    node->next->accept(this);
    addSingleValue("Load");
}

void TerminalTracePrinter::visit(TraceEndSuccess* node)
{
    // Nowhere to go from here.
    addSingleValue("End (S)");
}

void TerminalTracePrinter::visit(TraceEndFailure* node)
{
    // Nowhere to go from here.
    addSingleValue("End (F)");
}

void TerminalTracePrinter::visit(TraceEndUnknown* node)
{
    // Nowhere to go from here.
    addSingleValue("End (?)");
}


// Add a single "pass-through" node to the top of the current tree.
void TerminalTracePrinter::addSingleValue(QString nodeText)
{
    nodeText = "[" + nodeText + "]";

    if(mCurrentTree.lines.empty()){
        // Then we start a new tree
        mCurrentTree.lines.append(nodeText);
        mCurrentTree.width = nodeText.length();
        mCurrentTree.connector = mCurrentTree.width / 2;

    }else{
        // Then we add to an existing tree.
        if(nodeText.length() <= mCurrentTree.width){
            // Pad the node text (making sure it will be exactly mCurrentTree.width chars in all)
            nodeText = padToConnector(nodeText, mCurrentTree.connector, mCurrentTree.width);
            //QString leftPad = QString((mCurrentTree.width - nodeText.length()) / 2, ' ');
            //QString rightPad = QString(mCurrentTree.width - nodeText.length() - leftPad.length(), ' ');
            //nodeText.prepend(leftPad);
            //nodeText.append(rightPad);

        }else{
            QString leftPad = QString((nodeText.length() - mCurrentTree.width) / 2, ' ');
            QString rightPad = QString(nodeText.length() - mCurrentTree.width - leftPad.length(), ' ');
            // Pad the current tree (every line must be exaclty nodeText.length() chars in all)
            foreach(QString line, mCurrentTree.lines){
                line.prepend(leftPad);
                line.append(rightPad);
            }
            // Reset the width and connector position.
            mCurrentTree.width = nodeText.length();
            mCurrentTree.connector += leftPad.length();
        }

        // Insert the connector and then the node text itself.
        QString connectorLine = QString(mCurrentTree.width, ' ');
        connectorLine.replace(mCurrentTree.connector, 1, '|');
        mCurrentTree.lines.prepend(connectorLine);
        mCurrentTree.lines.prepend(nodeText);
        // Now mCurrentTree is properly formatted (an exact rectangle with all lines of equal length).
    }
}


// Merge two trees into a new tree.
void TerminalTracePrinter::addBranch(QString nodeText)
{
    // We already have the left subtree in the stack and the right (current) subtree.
    // Now we need to join them and create the branch.
    PrintableTree leftTree = mCompletedLeftTrees.pop();
    PrintableTree rightTree = mCurrentTree;
    mCurrentTree.clear();

    nodeText = "[" + nodeText + "]";
    QString spacing = QString(2, ' ');

    if(nodeText.length() > leftTree.width + rightTree.width + spacing.length()){
        // Then we will add some spacing between the trees when joining.
        spacing += QString(nodeText.length() - leftTree.width - rightTree.width - spacing.length());
        mCurrentTree.width = leftTree.width + spacing.length() + rightTree.width; // == nodeText.length().
        mCurrentTree.connector = mCurrentTree.width / 2;

    }else{
        // Then pad the node text.
        // Put it as close as possible to the point halfway beteen the left and right connectors.
        // However we will prefer to keep it within the correct width at all costs.
        int idealCentre = (leftTree.connector + leftTree.width + spacing.length() + rightTree.connector) / 2;

        mCurrentTree.width = leftTree.width + spacing.length() + rightTree.width;
        mCurrentTree.connector = idealCentre;

        nodeText = padToConnector(nodeText, idealCentre, mCurrentTree.width);

    }

    // Make the trees the same height.
    if(leftTree.lines.length() > rightTree.lines.length()){
        int numToAdd = leftTree.lines.length() - rightTree.lines.length();
        for(int i = 0; i < numToAdd; i++){
            rightTree.lines.append(QString(rightTree.width, ' '));
        }

    }else{
        int numToAdd = rightTree.lines.length() - leftTree.lines.length();
        for(int i = 0; i < numToAdd; i++){
            leftTree.lines.append(QString(leftTree.width, ' '));
        }
    }

    // Join the trees.
    for(int i = 0; i < leftTree.lines.length(); i++){
        mCurrentTree.lines.append(leftTree.lines.at(i) + spacing + rightTree.lines.at(i));
    }

    // Add the conectors, connecting line and new node.
    int leftConnector = leftTree.connector;
    int rightConnector = leftTree.width + spacing.length() + rightTree.connector;

    QString connectorLines = QString(mCurrentTree.width, ' ');
    connectorLines.replace(leftConnector, 1, '|');
    connectorLines.replace(rightConnector, 1, '|');

    QString connectorBar = QString(leftConnector, ' ') + "+" + QString(rightConnector - leftConnector - 1, '-') + "+" + QString(mCurrentTree.width - rightConnector, ' ');
    connectorBar.replace(mCurrentTree.connector, 1, '+');

    QString connectorTopLine = QString(mCurrentTree.width, ' ');
    connectorTopLine.replace(mCurrentTree.connector, 1, '|');

    mCurrentTree.lines.prepend(connectorLines);
    mCurrentTree.lines.prepend(connectorBar);
    mCurrentTree.lines.prepend(connectorTopLine);
    mCurrentTree.lines.prepend(nodeText);

}



QString TerminalTracePrinter::padToConnector(QString text, int connector, int width)
{
    // Pad the text to be eactly width ccharacters and as close as possible
    // to being centred over the connector within that.

    int idealStart = connector - (text.length() / 2);
    int idealEnd = idealStart + text.length();

    if(idealStart <= 0){
        // Pad only on the right.
        text.append(QString(width - text.length(), ' '));

    }else if(idealEnd >= width){
        // Pad only on the left.
        text.prepend(QString(width - text.length(), ' '));

    }else{
        // Pad on both sides.
        text.prepend(QString(idealStart, ' '));
        text.append(QString(width - idealEnd, ' '));
    }

    return text;
}




} // namespace artemis

