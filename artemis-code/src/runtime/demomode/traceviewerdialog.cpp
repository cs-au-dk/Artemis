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


#include "traceviewerdialog.h"

#include "concolic/solver/expressionprinter.h"
#include "util/loggingutil.h"


namespace artemis
{



TraceViewerDialog::TraceViewerDialog(TraceNodePtr trace, QWidget* parent) :
    QDialog(parent),
    mNodeList(new QListWidget())
{
    // Set up this dialog
    setWindowTitle("View Previous Trace");

    // Set up the list view used to display the trace items.
    mNodeList->addItem("Start");
    trace->accept(this);

    // Set up close button
    QDialogButtonBox* buttonBox = new QDialogButtonBox();
    buttonBox->addButton("Close", QDialogButtonBox::AcceptRole);
    connect(buttonBox, SIGNAL(accepted()), this, SLOT(accept()));

    // Set up layout/sizing
    QVBoxLayout* layout = new QVBoxLayout();
    layout->addWidget(mNodeList);
    layout->addWidget(buttonBox);
    setLayout(layout);
    setMinimumSize(500, 400);

}




/*
 *  Visitor part is used to add nodes to the GUI trace.
 */

void TraceViewerDialog::visit(TraceNode *node)
{
    // Should never be reached.
    Log::fatal("Trying to display a trace which includes unknown node types.");
    exit(1);
}

void TraceViewerDialog::visit(TraceConcreteBranch *node)
{
    // This printer only works for straight-line traces, so we require branches that one side is alwyas "capped"
    // by a TraceUnexplored node immediately.

    if(isImmediatelyUnexplored(node->getFalseBranch())){
        // Took 'true' branch.

        mNodeList->addItem("Branch: Took true branch;");
        node->getTrueBranch()->accept(this);

    } else if(isImmediatelyUnexplored(node->getTrueBranch())){
        // Took 'false' branch.

        mNodeList->addItem("Branch: Took false branch;");
        node->getFalseBranch()->accept(this);

    } else {
        // Invalid branch node

        Log::fatal("Trace Display: reached an invalid branch node.");
        exit(1);
    }
}

void TraceViewerDialog::visit(TraceSymbolicBranch *node)
{
    // This printer only works for straight-line traces, so we require branches that one side is alwyas "capped"
    // by a TraceUnexplored node immediately.

    ExpressionPrinter printer;
    node->getSymbolicCondition()->accept(&printer);

    if(isImmediatelyUnexplored(node->getFalseBranch())){
        // Took 'true' branch.

        mNodeList->addItem(QString("Branch: Condition: %1; Took true branch; Symbolic").arg(printer.getResult().data()));
        node->getTrueBranch()->accept(this);

    } else if(isImmediatelyUnexplored(node->getTrueBranch())){
        // Took 'false' branch.

        mNodeList->addItem(QString("Branch: Condition: %1; Took false branch; Symbolic").arg(printer.getResult().data()));
        node->getFalseBranch()->accept(this);

    } else {
        // Invalid branch node

        Log::fatal("Trace Display: reached an invalid branch node.");
        exit(1);
    }
}

void TraceViewerDialog::visit(TraceUnexplored *node)
{
    // Should not be reached.
    mNodeList->addItem("Unexplored");
}

void TraceViewerDialog::visit(TraceAlert *node)
{
    mNodeList->addItem(QString("Alert: %1").arg((node->message).replace('\n', "\\n")));
    node->next->accept(this);
}

void TraceViewerDialog::visit(TraceDomModification *node)
{
    mNodeList->addItem(QString("DOM Modification: %1%").arg(node->amountModified));
    node->next->accept(this);
}

void TraceViewerDialog::visit(TracePageLoad *node)
{
    mNodeList->addItem(QString("Page Load: %1").arg(node->page));
    node->next->accept(this);
}

void TraceViewerDialog::visit(TraceFunctionCall *node)
{
    mNodeList->addItem(QString("Function Call: %1").arg(node->name));
    node->next->accept(this);
}

void TraceViewerDialog::visit(TraceEndSuccess *node)
{
    mNodeList->addItem("End (Success)");
}

void TraceViewerDialog::visit(TraceEndFailure *node)
{
    mNodeList->addItem("End (Falure)");
}

void TraceViewerDialog::visit(TraceEndUnknown *node)
{
    mNodeList->addItem("End (Unknown)");
}



} //namespace artemis
