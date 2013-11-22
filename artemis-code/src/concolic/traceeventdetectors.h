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

#include <QString>
#include <QWebFrame>
#include <QSharedPointer>
#include <QSource>
#include <QWebExecutionListener>
#include <QPair>

#include "concolic/executiontree/tracenodes.h"

#ifndef TRACEEVENTDETECTORS_H
#define TRACEEVENTDETECTORS_H


namespace artemis
{


class TraceBuilder;


// I have put all the detectors into a single file for now, as I anticipate each of them being relatively simple.

// To be honest none of them keep any state, so they might as well all be in one class anyway. They have turned out to be much simpler than anticipated.


/*
 *  We have multiple types of trace event detectors which detect different "interesting events" and contribute
 *  new nodes to the trace builder.
 *  This class is extended by classes which will detect events, create trace nodes and call newNode on those nodes.
 */

class TraceEventDetector : public QObject
{
    Q_OBJECT

public:
    virtual ~TraceEventDetector(){}

    void setTraceBuilder(TraceBuilder* traceBuilder);

private:
    TraceBuilder* mTraceBuilder; // Must use standard pointer as this is set via the 'this' pointer of the parent trace builder.
    // TODO: can probably be a QWeakPointer? Still should not be QSharedPointer to avoid a circular reference.

protected:
    // See TraceBuilder::newNode comment in tracebuilder.h.
    void newNode(QSharedPointer<TraceNode> node, QSharedPointer<TraceNode>* successor);
};




/*
 *  Detector for branch events.
 */
class TraceBranchDetector : public TraceEventDetector
{
    Q_OBJECT

protected slots:
    void slBranch(bool jump, Symbolic::Expression* condition, uint sourceOffset, QSource* source, const ByteCodeInfoStruct byteInfo);
};




/*
 *  Detector for alert() calls.
 */
class TraceAlertDetector : public TraceEventDetector
{
    Q_OBJECT

public slots:
    void slJavascriptAlert(QWebFrame *frame, QString msg);

};



/*
 *  Detector for application-code function calls.
 */
class TraceFunctionCallDetector : public TraceEventDetector
{
    Q_OBJECT

public slots:
    void slJavascriptFunctionCalled(QString functionName, size_t bytecodeSize, uint functionStartLine, uint sourceOffset, QSource* source);

};



/*
 *  Detector for page loads.
 */
class TracePageLoadDetector : public TraceEventDetector
{
    Q_OBJECT

public slots:
    void slPageLoad(QUrl url);
};


/*
 *  Detector for DOM modifications.
 *  Currently this is used as a "batch" notification of all changes at the end of a trace.
 */
class TraceDomModDetector : public TraceEventDetector
{
    Q_OBJECT

public slots:
    void slDomModified(QString start, QString end);

private:
    static QPair<double, QMap<int, int> > computeMetrics(QString start, QString end);
    static QStringList tokenise(QString dom);
    static QPair<int, QStringList> findInsertions(QStringList start, QStringList end);

    static QList<QString> getIndicators();

public:
    static const QList<QString> indicators;
};



} // namespace artemis

#endif // TRACEEVENTDETECTORS_H
