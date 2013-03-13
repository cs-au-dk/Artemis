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
#include "pathtracer.h"
#include "util/loggingutil.h"


namespace artemis{

PathTracer::PathTracer()
{
    mTraces = QList<PathTrace>();
}

void PathTracer::notifyStartingLoad()
{
    newPathTrace("Starting Page Load");
}

void PathTracer::notifyStartingEvent(QSharedPointer<const BaseInput> inputEvent)
{
    newPathTrace("Starting Event: " + (inputEvent->toString()));
}

void PathTracer::slJavascriptFunctionCalled(QString functionName, size_t bytecodeSize, uint sourceOffset, QUrl sourceUrl, uint sourceStartLine)
{
    name = name.isEmpty() ? "<no name>" : (name + "()"); // Anonymous function??
    appendItem(FUNCALL, name);
}

void PathTracer::newPathTrace(QString event)
{
    QList<QPair<PathTracer::ItemType, QString> > nl = QList<QPair<PathTracer::ItemType, QString> >();
    PathTrace newTrace = qMakePair(event, nl);
    mTraces.append(newTrace);
}

void PathTracer::appendItem(ItemType type, QString message)
{
    if(mTraces.isEmpty()){
        newPathTrace("<No Event Yet>");
    }
    mTraces.last().second.append(qMakePair(type, message));
}

void PathTracer::write()
{
    QPair<ItemType,QString> item;
    PathTrace trace;

    //Log::info("===== Path Tracer =====");
    if(mTraces.isEmpty()){
        Log::info("No traces were recorded");
        return;
    }
    foreach(trace, mTraces){
        Log::info("Trace: " + trace.first.toStdString());
        foreach(item, trace.second){
            switch(item.first){
            case FUNCALL:
                Log::info("  Function Call: " + item.second.toStdString());
                break;
            default:
                Log::info("  Unknown:       " + item.second.toStdString());
                break;
            }
        }
    }
}

}
