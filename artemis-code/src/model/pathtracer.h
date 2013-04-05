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
#ifndef PATHTRACER_H
#define PATHTRACER_H

#include <string>
#include <inttypes.h>

#include <QObject>
#include <QList>
#include <QSharedPointer>
#include <QUrl>
#include <QWebElement>
#include <QWebExecutionListener>
#include <QDateTime>
#include <QListIterator>

#include "runtime/options.h"
#include "runtime/input/baseinput.h"

namespace artemis
{

class PathTracer : public QObject
{
    Q_OBJECT

public:
    explicit PathTracer(PathTraceReport reportLevel, bool reportBytecode);
    void notifyStartingLoad();
    void notifyStartingEvent(QSharedPointer<const BaseInput> inputEvent);
    void write();
    void writePathTraceHTML();

private:
    enum ItemType {FUNCALL, FUNRET, BYTECODE, ALERT};
    struct TraceItem {
        ItemType type;
        QString name;
        // The following are not present in all item types.
        QUrl sourceUrl;
        uint sourceOffset, sourceStartLine, lineInFile, bytecodeOffset;
        QString message;
    };
    enum TraceType {OTHER, CLICK, PAGELOAD};
    struct PathTrace {
        TraceType type;
        QString description;
        QList<TraceItem> items;
    };

    QList<PathTrace> mTraces;
    const PathTraceReport mReportLevel;
    const bool mReportBytecode;

    void newPathTrace(QString description, TraceType type);
    void appendItem(TraceItem item);
    void appendItem(ItemType type, QString name, QString message);

    QString displayedUrl(QUrl url, bool fileNameOnly = false);
    QString displayedFunctionName(QString name);

public slots:
    void slJavascriptFunctionCalled(QString functionName, size_t bytecodeSize, uint sourceOffset, QUrl sourceUrl, uint sourceStartLine, uint functionStartLine);
    void slJavascriptFunctionReturned(QString functionName);
    void slJavascriptBytecodeExecuted(const QString& bytecode, bool isSymbolic, uint bytecodeOffset, uint sourceOffset, const QUrl& sourceUrl, uint sourceStartLine);
    void slEventListenerTriggered(QWebElement* elem, QString eventName);
    void slJavascriptAlert(QWebFrame* frame, QString msg);

};

typedef QSharedPointer<PathTracer> PathTracerPtr;

}

#endif // PATHTRACER_H
