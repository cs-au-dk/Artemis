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


// Base Detector Class

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

void TraceEventDetector::newSummaryInfo(TraceConcreteSummarisation::EventType info)
{
    if(mTraceBuilder){
        mTraceBuilder->newSummaryInfo(info);
    }else{
        Log::fatal("Trace Event Detector being used with no associated Trace Builder.");
        exit(1);
    }
}

bool TraceEventDetector::shouldSummarise()
{
    if(mTraceBuilder){
        return mTraceBuilder->shouldSummarise();
    }else{
        Log::fatal("Trace Event Detector being used with no associated Trace Builder.");
        exit(1);
    }
}



// Branch Detector


void TraceBranchDetector::slBranch(bool jump, Symbolic::Expression* condition, uint sourceOffset, QSource* source, const ByteCodeInfoStruct byteInfo)
{
    // Concrete branches can be summarised. Check if the trace builder requests this.
    if(shouldSummarise() && condition == NULL) {
        if(jump){
            newSummaryInfo(TraceConcreteSummarisation::BRANCH_TRUE);
        }else{
            newSummaryInfo(TraceConcreteSummarisation::BRANCH_FALSE);
        }
        return;
    }

    QSharedPointer<TraceBranch> node;

    if (condition == NULL) {
        // concrete branch
        node = QSharedPointer<TraceBranch>(new TraceConcreteBranch(sourceOffset, source, byteInfo.linenumber));
    } else {
        // symbolic branch
        node = QSharedPointer<TraceBranch>(new TraceSymbolicBranch(condition, sourceOffset, source, byteInfo.linenumber));
    }

    // Set the branch we did not take to "unexplored". The one we took is left null.
    // Pass this new node to the trace builder and the branch pointer to use as a successor.
    if(jump){
        newNode(node, &(node->mBranchTrue));
    }else{
        newNode(node, &(node->mBranchFalse));
    }

}



// Alert Detector

void TraceAlertDetector::slJavascriptAlert(QWebFrame* frame, QString msg)
{
    // Create a new alert node.
    QSharedPointer<TraceAlert> node = QSharedPointer<TraceAlert>(new TraceAlert());
    node->message = msg;
    // Leave node.next as null.

    // Pass this new node to the trace builder and pass a pointer to where the sucessor should be attached.
    newNode(node.staticCast<TraceNode>(), &(node->next));
}





// Function Call Detector

void TraceFunctionCallDetector::slJavascriptFunctionCalled(QString functionName, size_t bytecodeSize, uint functionStartLine, uint sourceOffset, QSource* source)
{
    // Function calls can be summarised. Check if the trace builder requests this.
    if(shouldSummarise()) {
        newSummaryInfo(TraceConcreteSummarisation::FUNCTION_CALL);
        return;
    }

    // Create a new function call node.
    QSharedPointer<TraceFunctionCall> node = QSharedPointer<TraceFunctionCall>(new TraceFunctionCall());
    node->name = functionName;
    // Leave node.next as null.

    // Pass this new node to the trace builder and pass a pointer to where the sucessor should be attached.
    newNode(node.staticCast<TraceNode>(), &(node->next));
}



// Page Load Detector

void TracePageLoadDetector::slPageLoad(QUrl url)
{
    // Create the trace node.
    QSharedPointer<TracePageLoad> node  = QSharedPointer<TracePageLoad>(new TracePageLoad());
    node->url = url;

    // Pass the new node to the trace builder.
    newNode(node.staticCast<TraceNode>(), &(node->next));
}



/* DOM Modification Detector */

void TraceDomModDetector::slDomModified(QString start, QString end)
{
    // Create the node.
    QSharedPointer<TraceDomModification> node = QSharedPointer<TraceDomModification>(new TraceDomModification());

    QPair<double, QMap<int, int> > metrics = computeMetrics(start, end);
    node->amountModified = metrics.first;
    node->words = metrics.second;

    // Pass the new node to the trace builder.
    newNode(node.staticCast<TraceNode>(), &(node->next));
}


// Takes the two DOM strings and computes the modification metrics.
// Returns a pair or the amount of modification and the list of indicator words which were added.
QPair<double, QMap<int, int> > TraceDomModDetector::computeMetrics(QString start, QString end)
{
    QStringList startTokens = tokenise(start);
    QStringList endTokens = tokenise(end);

    //Log::debug(startTokens.join("\n").toStdString());

    QPair<int, QStringList> result = findInsertions(startTokens, endTokens);

    Log::debug(QString("Edit distance between DOMs: %1").arg(result.first).toStdString());
    //Log::debug("Inserted words:");
    //Log::debug(result.second.join("\n").toStdString());

    // Compute the metric of "amount modified". This is not a true percentage, and can even be over 100!
    double modified = 100.0 * (double)result.first / startTokens.length();
    Log::debug(QString("Amount modified: %2/%3 = %1%").arg(modified).arg((double)result.first).arg((double)startTokens.length()).toStdString());

    // Check whether any of the inserted words are in our "indicators" list.
    QMap<int,int> matches;
    int j;
    foreach(QString inserted, result.second) {
        for(j = 0; j < indicators.length(); j++) {
            if(inserted.compare(indicators.at(j), Qt::CaseInsensitive) == 0) {
                matches.insert(j, 1 + matches.value(j, 0));
                Log::debug(QString("On list: %1").arg(inserted).toStdString());
            }
        }
    }

    return QPair<double,QMap<int,int> >(modified, matches);
}

// Splits a DOM string into tokens.
// We split on whitespace and a few HTML characters which will get the text into decently small chunks.
// Also split on a bunch of punctuation to increase the chance we islate the important words
// It is not super-important exactly how we define the tokens.
QStringList TraceDomModDetector::tokenise(QString dom)
{
    QRegExp delimiters("\\s+|<|>|\"|'|:|\\.|,|!|\\?|/|;|-");
    return dom.split(delimiters, QString::SkipEmptyParts);
}

// Take two tokenised streams and compute the edit distance (and edits).
QPair<int, QStringList> TraceDomModDetector::findInsertions(QStringList start, QStringList end)
{
    int i,j;
    // This is a pretty simple implementation for now.
    // I am also only using insertions and deletions (no substitutions). This is because we want a list of what was added and removed, so substitutions are not interesting (and would just add something to both lists anyway).

    // Create an array of the distances between each pair of subsequences. Pre-fill with 0s.
    QVector<QVector<int> > distance(start.length()+1, QVector<int>(end.length()+1, 0));

    // Pre-fill edges with counts 0,1,2,3,...
    for(i = 1; i <= start.length(); i++) {
        distance[i][0] = i;
    }
    for(j = 1; j <= end.length(); j++) {
        distance[0][j] = j;
    }

    // Fill in the matrix row-by-row.
    for(j = 1; j <= end.length(); j++) {
        for(i = 1; i <= start.length(); i++) {
            // If the strings match at this point, then we don't need to do anything. N.B. String indexing is off by one from matrix indexing.
            if(start.at(i-1).compare(end.at(j-1)) == 0){
                distance[i][j] = distance[i-1][j-1];
            }else{
                // Otherwise, we choose whichever of a deletion or insertion is cheapest.
                distance[i][j] = min(distance[i-1][j] + 1, distance[i][j-1] + 1);
            }
        }
    }

    // Now the edit distance is:
    int editDistance = distance[start.length()][end.length()];


    // To work out the actual edits, we need to backtrack through the table.
    // We start at the bottom right of the matrix and look for cells with the same or one-lower cost which we can move to.
    // In this case we are not really interested in the exact solution, just a list of what was added.
    QStringList insertedWords;
    i = start.length();
    j = end.length();
    while(i > 0 || j > 0) {
        // If the diagonally-backwards cell d[i-1,j-1] has the same value as d[i,j] and it's the lowes adjacent cell then it is a match which we can ignore.
        if(i > 0 && j > 0 && distance[i][j] == distance[i-1][j-1] && distance[i-1][j-1] <= distance[i-1][j] && distance[i-1][j-1] <= distance[i][j-1]){
            i--;
            j--;
        } else if(j > 0 && distance[i][j] == distance[i][j-1] + 1) {
            // Then we have an insertion here.
            insertedWords.append(end.at(j-1));
            j--;
        } else if(i > 0 && distance[i][j] == distance[i-1][j] + 1) {
            // Then we have a deletion here.
            i--;
        } else {
            // Should never be reached, assuming the matrix was filled correctly.
            Log::error("Error in TraceDomModDetector::findInsertions() while computing DOM modifications.");
            break;
        }
    }

    return QPair<int, QStringList>(editDistance, insertedWords);
}

// The definition of which words we consider interesting indicators of an error.
// The comparisons are case-insensitive so case does not matter here.
QList<QString> TraceDomModDetector::getIndicators()
{
    QList<QString> words;
    words.append("Error");
    words.append("Please");
    words.append("Problem");
    words.append("Warning");
    words.append("Valid");
    words.append("Invalid");
    words.append("Required");
    words.append("Require");
    words.append("Sorry");
    words.append("Field");
    words.append("Selected");
    words.append("Select");
    words.append("Enter");
    words.append("Important");
    words.append("Correct");
    words.append("Incorrect");
    return words;
}
const QList<QString> TraceDomModDetector::indicators = TraceDomModDetector::getIndicators();




// Trace Marker Detector

void TraceMarkerDetector::slNewMarker(QString label, QString index, bool isSelectRestriction, SelectRestriction selectRestriction)
{
    // Create the trace node.
    QSharedPointer<TraceMarker> node  = QSharedPointer<TraceMarker>(new TraceMarker());
    node->label = label;
    node->index = index;
    node ->isSelectRestriction = isSelectRestriction;
    node ->selectRestriction = selectRestriction;

    // Pass the new node to the trace builder.
    newNode(node.staticCast<TraceNode>(), &(node->next));
}



} //namespace artmeis
