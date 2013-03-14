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
#include <QPair>
#include <QSharedPointer>
#include <QUrl>
#include <QWebElement>

#include "runtime/input/baseinput.h"

namespace artemis
{

class PathTracer : public QObject
{
    Q_OBJECT

public:
    explicit PathTracer();
    void notifyStartingLoad();
    void notifyStartingEvent(QSharedPointer<const BaseInput> inputEvent);
    void write();

private:
    enum ItemType {FUNCALL, FUNRET};
    typedef QPair<QString, QList<QPair<PathTracer::ItemType, QString> > > PathTrace;
    QList<PathTrace> mTraces;
    void newPathTrace(QString event);
    void functionCall(QString name);
    void appendItem(ItemType type, QString message);

public slots:
    void slJavascriptFunctionCalled(QString functionName, size_t bytecodeSize, uint sourceOffset, QUrl sourceUrl, uint sourceStartLine);
    void slJavascriptFunctionReturned(QString functionName, size_t bytecodeSize, uint sourceOffset, QUrl sourceUrl, uint sourceStartLine);
    void slEventListenerTriggered(QWebElement* elem, QString eventName);
};

typedef QSharedPointer<PathTracer> PathTracerPtr;

}

#endif // PATHTRACER_H
