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

#ifndef PATHTRACER_H
#define PATHTRACER_H

#include <string>
#include <inttypes.h>

#include <QObject>
#include <QList>
#include <QSharedPointer>
#include <QWebElement>
#include <QWebExecutionListener>
#include <QDateTime>
#include <QListIterator>
#include <QSource>
#include <QHash>

#include "runtime/options.h"
#include "runtime/input/baseinput.h"
#include "model/coverage/sourceinfo.h"
#include "model/coverage/coveragelistener.h"

namespace artemis
{

class PathTracer : public QObject
{
    Q_OBJECT

public:
    explicit PathTracer(PathTraceReport reportLevel, CoverageListenerPtr coverage);
    void notifyStartingLoad();
    void notifyStartingEvent(QSharedPointer<const BaseInput> inputEvent);
    void write();
    void writePathTraceHTML(bool linkWithCoverage, QString coveragePath, QString& pathToFile);
    void writeStatistics();

private:

    CoverageListenerPtr mCoverage; // used for printing urls without storing the entire URL

    enum ItemType {FUNCALL, FUNRET, ALERT};
    struct TraceItem {
        ItemType type;
        QString string;

        // The following are not present in all item types.
        uint lineInFile;
        sourceid_t sourceID;

        QString getUrl(CoverageListenerPtr coverage) {
            return coverage->getSourceInfo(sourceID)->getURL();
        }

        QString getName() {
            switch (type) {
            case ALERT:
                return "alert()";
            default:
                return string;
            }
        }

        QString getMessage(CoverageListenerPtr coverage) {
            switch (type) {
            case FUNCALL:
                return QString("File: %1, Line: %2.").arg(PathTracer::displayedUrl(getUrl(coverage))).arg(lineInFile);
            case ALERT:
                return string;
            default:
                return "";
            }
        }

        uint hashcode() {
            return (uint)type + qHash(string) * 7 + lineInFile * 31 + sourceID * 79;
        }
    };

    /**
     * We place all trace items in the trace item pool, such that items with identical contents are merged together.
     *
     * This is to reduce the high memory consumption resulting from a large number of very similar traces.
     */
    typedef uint TraceItemReference;
    QHash<TraceItemReference, TraceItem> mTraceItemPool;

    unsigned int mTraceItemPoolUncompressedSize;

    enum TraceType {OTHER, CLICK, LOAD, MOUSE};
    struct PathTrace {
        TraceType type;
        QString description;
        QList<TraceItemReference> items;
    };

    QList<PathTrace> mTraces;
    const PathTraceReport mReportLevel;

    void newPathTrace(QString description, TraceType type);
    void appendItem(TraceItem item);
    void appendItem(ItemType type, QString name);

    static QString displayedUrl(QString url, bool fileNameOnly = false);
    QString displayedFunctionName(QString name);
    QString TraceClass(TraceType type);

public slots:
    void slJavascriptFunctionCalled(QString functionName, size_t bytecodeSize, uint functionStartLine, uint sourceOffset, QSource* source);
    void slJavascriptFunctionReturned(QString functionName);
    void slEventListenerTriggered(QWebElement* elem, QString eventName);
    void slJavascriptAlert(QWebFrame* frame, QString msg);
};

typedef QSharedPointer<PathTracer> PathTracerPtr;

}

#endif // PATHTRACER_H
