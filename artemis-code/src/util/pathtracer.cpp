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

#include "util/loggingutil.h"
#include "util/pathtracer.h"

namespace artemis{

QList<PathTracer::PathTrace> PathTracer::traces = QList<PathTracer::PathTrace>();

void PathTracer::newPathTrace(string event)
{
    QList<QPair<PathTracer::ItemType, string> > nl = QList<QPair<PathTracer::ItemType, string> >();
    PathTrace newTrace = qMakePair(event, nl);
    traces.append(newTrace);
}

void PathTracer::functionCall(string name)
{
    name = name.empty() ? "<no name>" : (name + "()");
    appendItem(FUNCALL, name);
}

// Idea is to have more methods similar to functionCall() in future.
// Each one can also be extended to include context info as required.

void PathTracer::appendItem(ItemType type, string message)
{
    if(traces.isEmpty()){
        newPathTrace("No Event Yet");
    }
    traces.last().second.append(qMakePair(type, message));
}

void PathTracer::write()
{
    QPair<ItemType,string> item;
    PathTrace trace;

    //Log::info("===== Path Tracer =====");
    if(traces.isEmpty()){
        Log::info("No traces were recorded");
        return;
    }
    foreach(trace, traces){
        Log::info("Trace: " + trace.first);
        foreach(item, trace.second){
            switch(item.first){
            case FUNCALL:
                Log::info("  Function Call: " + item.second);
                break;
            default:
                Log::info("  Unknown:       " + item.second);
                break;
            }
        }
    }
}

}
