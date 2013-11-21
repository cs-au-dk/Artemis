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

#include <assert.h>

#include "traceeventdetectors.h"
#include "concolic/executiontree/tracebuilder.h"

#include "util/loggingutil.h"


namespace artemis
{


/* Base Detector Class *******************************************************/

void TraceEventDetector::setTraceBuilder(TraceBuilder* traceBuilder)
{
    mTraceBuilder = traceBuilder;
}

void TraceEventDetector::newNode(QSharedPointer<TraceNode> node, QSharedPointer<TraceNode>* successor)
{
    if(mTraceBuilder){
        mTraceBuilder->newNode(node, successor);
    }else{
        Log::fatal("Trace Event Detector being used with no associated Trace Builder.");
        exit(1);
    }
}



/* Branch Detector ***********************************************************/


void TraceBranchDetector::slBranch(bool jump, Symbolic::Expression* condition, uint sourceOffset, QSource* source, const ByteCodeInfoStruct byteInfo)
{
    QSharedPointer<TraceBranch> node;

    if (condition == NULL) {
        // concrete branch
        node = QSharedPointer<TraceBranch>(new TraceConcreteBranch());
    } else {
        // symbolic branch
        node = QSharedPointer<TraceBranch>(new TraceSymbolicBranch(condition));
    }

    // Set the branch we did not take to "unexplored". The one we took is left null.
    // Pass this new node to the trace builder and the branch pointer to use as a successor.
    if(jump){
        newNode(node, &(node->mBranchTrue));
    }else{
        newNode(node, &(node->mBranchFalse));
    }
}



/* Alert Detector ************************************************************/

void TraceAlertDetector::slJavascriptAlert(QWebFrame* frame, QString msg)
{
    // Create a new alert node.
    QSharedPointer<TraceAlert> node = QSharedPointer<TraceAlert>(new TraceAlert());
    node->message = msg;
    // Leave node.next as null.

    // Pass this new node to the trace builder and pass a pointer to where the sucessor should be attached.
    newNode(node.staticCast<TraceNode>(), &(node->next));
}





/* Function Call Detector ****************************************************/

void TraceFunctionCallDetector::slJavascriptFunctionCalled(QString functionName, size_t bytecodeSize, uint functionStartLine, uint sourceOffset, QSource* source)
{
    // Create a new function call node.
    QSharedPointer<TraceFunctionCall> node = QSharedPointer<TraceFunctionCall>(new TraceFunctionCall());
    node->name = functionName;
    // Leave node.next as null.

    // Pass this new node to the trace builder and pass a pointer to where the sucessor should be attached.
    newNode(node.staticCast<TraceNode>(), &(node->next));
}



/* Page Load Detector ********************************************************/

void TracePageLoadDetector::slPageLoad(QUrl url)
{
    // Create the trace node.
    QSharedPointer<TracePageLoad> node  = QSharedPointer<TracePageLoad>(new TracePageLoad());
    node->url = url;

    // Pass the new node to the trace builder.
    newNode(node.staticCast<TraceNode>(), &(node->next));
}





} //namespace artmeis
