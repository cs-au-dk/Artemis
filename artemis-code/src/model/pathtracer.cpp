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

PathTracer::PathTracer(PathTraceReport reportLevel, bool reportBytecode) :
    mTraces(QList<PathTrace>()),
    mReportLevel(reportLevel),
    mReportBytecode(reportBytecode),
    mCurrentlyRecording(reportLevel != ALL_TRACES)
{
}

void PathTracer::notifyStartingLoad()
{
    // Record this for *any* setting of mCurrentlyReporting.
    newPathTrace("Starting Page Load");
}

// An event which Artemis is triggering.
// TODO: Maybe obsolete since we have slEventListenerTriggered below?
void PathTracer::notifyStartingEvent(QSharedPointer<const BaseInput> inputEvent)
{
    QString eventStr = inputEvent->toString();
    // TODO: is there a better way to check for inputEvent being a click without adding a special method to BaseInput?
    if(mReportLevel == ALL_TRACES || ( mReportLevel == CLICK_TRACES && eventStr.startsWith("DomInput(click"))) {
        mCurrentlyRecording = true;
        newPathTrace("Starting Event: " + eventStr);
    }else{
        mCurrentlyRecording = false;
    }

}

// An event which WebKit is executing.
void PathTracer::slEventListenerTriggered(QWebElement* elem, QString eventName)
{
    if(mReportLevel == ALL_TRACES || ( mReportLevel == CLICK_TRACES && eventName == "click")) {
        mCurrentlyRecording = true;
        newPathTrace("Received Event: '" + eventName + "' on '" + elem->tagName() + "'");
    } else {
        mCurrentlyRecording = false;
    }
}

void PathTracer::slJavascriptFunctionCalled(QString functionName, size_t bytecodeSize, uint sourceOffset, QUrl sourceUrl, uint sourceStartLine)
{
    functionName = functionName.isEmpty() ? "<no name>" : (functionName + "()"); // Anonymous function??
    appendItem(FUNCALL, functionName);
}

void PathTracer::slJavascriptFunctionReturned(QString functionName, size_t bytecodeSize, uint sourceOffset, QUrl sourceUrl, uint sourceStartLine)
{
    functionName = functionName.isEmpty() ? "<no name>" : (functionName + "()"); // Anonymous function??
    appendItem(FUNRET, functionName);
}

void PathTracer::slJavascriptBytecodeExecuted(const QString& opcode, uint bytecodeOffset, uint sourceOffset, const QUrl& sourceUrl, uint sourceStartLine)
{
    if(mReportBytecode){
        appendItem(BYTECODE, opcode);
    }
}

void PathTracer::newPathTrace(QString description)
{
    if(mCurrentlyRecording) {
        QList<QPair<PathTracer::ItemType, QString> > newItemList = QList<QPair<PathTracer::ItemType, QString> >();
        PathTrace newTrace = qMakePair(description, newItemList);
        mTraces.append(newTrace);
    }
}

void PathTracer::appendItem(ItemType type, QString message)
{
    if(mTraces.isEmpty()){
        newPathTrace("<onload>");
    }
    if(mCurrentlyRecording) {
        mTraces.last().second.append(qMakePair(type, message));
    }
}

/**
  Note that this function implies a call graph which is not *necessarily* accurate.
  The function traces are given in chronological order, so if we ever get calls which are not sequential or
  for some reason we miss one then we will guess
**/
void PathTracer::write()
{
    QPair<ItemType,QString> item;
    PathTrace trace;
    uint stackLevel;

    //Log::info("===== Path Tracer =====");
    if(mTraces.isEmpty()){
        Log::info("No traces were recorded");
        return;
    }
    foreach(trace, mTraces){

        Log::info("    Trace Start | " + trace.first.toStdString());
        stackLevel = 0;

        foreach(item, trace.second){
            switch(item.first){
            case FUNCALL:
                Log::info("  Function Call | " + std::string(stackLevel*2, ' ') + item.second.toStdString());
                stackLevel++;
                break;
            case FUNRET:
                stackLevel--;
                //Log::info("  Function End:  " + std::string(stackLevel*2, ' ') + item.second.toStdString());
                break;
            case BYTECODE:
                Log::info("                | " + std::string(stackLevel*2, ' ') + item.second.toStdString());
                break;
            default:
                Log::info("  Unknown:       " + item.second.toStdString());
                break;
            }
        }

        Log::info("\n");
    }
}

}
