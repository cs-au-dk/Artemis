#include "traceeventdetectors.h"
#include "tracebuilder.h"



namespace artemis
{


/* Base Detector Class *******************************************************/

void TraceEventDetector::newNode(QSharedPointer<TraceNode> node, QSharedPointer<TraceNode>* successor)
{
    mTraceBuilder->newNode(node, successor);
}



/* Branch Detector ***********************************************************/


void TraceBranchDetector::slBranch()
{
    // Create a new branch node.

    // Set the branch we did not take to "unexplored". The one we took is null.

    // Pass this new node to the trace builder and the branch pointer to use as a successor.

    // TODO
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





} //namespace artmeis
