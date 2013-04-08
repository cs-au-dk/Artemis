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
#include "util/fileutil.h"
#include "model/coverage/codeblockinfo.h"

namespace artemis{

PathTracer::PathTracer(PathTraceReport reportLevel, bool reportBytecode) :
    mTraces(QList<PathTrace>()),
    mReportLevel(reportLevel),
    mReportBytecode(reportBytecode)
{
}

void PathTracer::notifyStartingLoad()
{
    newPathTrace("Starting Page Load", PAGELOAD);
}

// An event which Artemis is triggering.
// TODO: Maybe obsolete since we have slEventListenerTriggered below?
void PathTracer::notifyStartingEvent(QSharedPointer<const BaseInput> inputEvent)
{
    QString eventStr = inputEvent->toString();
    // TODO: is there a better way to check for inputEvent being a click without adding a special method to BaseInput?
    TraceType type = eventStr.startsWith("DomInput(click") ? CLICK : OTHER;
    newPathTrace("Starting Event: " + eventStr, type);
}

// An event which WebKit is executing.
void PathTracer::slEventListenerTriggered(QWebElement* elem, QString eventName)
{
    TraceType type = eventName == "click" ? CLICK : OTHER;
    newPathTrace("Received Event: '" + eventName + "' on '" + elem->tagName() + "'", type);
}

void PathTracer::slJavascriptFunctionCalled(QString functionName, size_t bytecodeSize, uint sourceOffset, QUrl sourceUrl, uint sourceStartLine, uint functionStartLine)
{
    TraceItem item;
    item.type = FUNCALL;
    item.name = displayedFunctionName(functionName);
    item.message = QString("File: %1, Line: %2.").arg(displayedUrl(sourceUrl)).arg(functionStartLine);
    item.sourceUrl = sourceUrl;
    item.sourceOffset = sourceOffset;
    item.sourceStartLine = sourceStartLine;
    item.lineInFile = functionStartLine;
    appendItem(item);
}

void PathTracer::slJavascriptFunctionReturned(QString functionName)
{
    appendItem(FUNRET, displayedFunctionName(functionName), "");
}

void PathTracer::slJavascriptBytecodeExecuted(const QString& opcode, bool isSymbolic, uint bytecodeOffset, uint sourceOffset, const QUrl& sourceUrl, uint sourceStartLine)
{
    TraceItem item;
    item.type = BYTECODE;
    item.name = opcode;
    item.message = isSymbolic ? "Symbolic" : "";
    item.sourceUrl = sourceUrl;
    item.sourceOffset = sourceOffset;
    item.sourceStartLine = sourceStartLine;
    item.bytecodeOffset = bytecodeOffset;
    appendItem(item);
}

void PathTracer::slJavascriptAlert(QWebFrame* frame, QString msg)
{
    msg = msg.replace("\n", "\\n");
    appendItem(ALERT, "alert()",  "Message: " + msg);
}

void PathTracer::newPathTrace(QString description, TraceType type)
{
    PathTrace newTrace;
    newTrace.type = type;
    newTrace.description = description;
    newTrace.items = QList<TraceItem>();
    mTraces.append(newTrace);
}

void PathTracer::appendItem(TraceItem item)
{
    if(mTraces.isEmpty()){
        Log::error("Error: Trace item was added before any trace was started.");
        Log::error("       Name: " + item.name.toStdString());
        exit(1);
    }
    mTraces.last().items.append(item);
}

void PathTracer::appendItem(ItemType type, QString name, QString message)
{
    TraceItem item;
    item.type = type;
    item.name = name;
    item.message = message;
    appendItem(item);
}

void PathTracer::write()
{
    TraceItem item;
    PathTrace trace;
    uint stackLevel;
    string itemStr;

    if(mReportLevel == NO_TRACES){
        return;
    }
    if(mReportLevel == HTML_TRACES){
        Log::info("Trace report will be output as an HTML file in the working directory.");
    }

    //Log::info("===== Path Tracer =====");
    if(mTraces.isEmpty()){
        Log::info("No traces were recorded.");
        return;
    }
    foreach(trace, mTraces){
        if(mReportLevel == ALL_TRACES || (mReportLevel == CLICK_TRACES && trace.type == CLICK)){

            Log::info("    Trace Start | " + trace.description.toStdString());
            stackLevel = 1;

            foreach(item, trace.items){
                if(item.message == ""){
                    itemStr = item.name.toStdString();
                }else{
                    itemStr = (item.name.leftJustified(35 - stackLevel*2) + ' ' + item.message).toStdString();
                }
                switch(item.type){
                case FUNCALL:
                    Log::info("  Function Call | " + std::string(stackLevel*2, ' ') + itemStr);
                    stackLevel++;
                    break;
                case FUNRET:
                    stackLevel--;
                    //Log::info("   Function End | " + std::string(stackLevel*2, ' ') + itemStr);
                    break;
                case BYTECODE:
                    if(mReportBytecode){
                        Log::info("                | " + std::string(stackLevel*2, ' ') + itemStr);
                    }
                    break;
                case ALERT:
                    Log::info("     Alert Call | " + std::string(stackLevel*2, ' ') + itemStr);
                    break;
                default:
                    Log::info("        Unknown | " + std::string(stackLevel*2, ' ') + itemStr);
                    break;
                }
            }

            Log::info("\n");
        }
    }
}

void PathTracer::writePathTraceHTML(){
    TraceItem item, peek;
    PathTrace trace;
    QString itemStr;
    QString extraStr, functionLink;
    uint indentLevel;
    QString indent;
    QString traceClass;

    QString style = ".controls a{text-decoration:underline;cursor:pointer;}.hidden{display:none;}ol{list-style:none;}ol.tracelist{margin-left:170px;}ol.tracelist>li{margin-bottom:30px;}ol.tracelist>li>span.label{font-weight:bold;}ol.functionbody{border-left:1px solid lightgray;}span.label{position:absolute;left:0;display:block;width:150px;text-align:right;}span.extrainfo{position:absolute;left:700px;white-space:nowrap;}span.itemname{font-family:monospace;}li.funcall>span.itemname,li.trace>span.description{cursor:pointer;margin-left:-1.2em;}li.funcall>span.itemname:before{content:'\\25BD\\00A0';}li.trace>span.description:before{content:'\\25BF\\00A0';}li.funcall.collapsed>span.itemname:before{content:'\\25B7\\00A0';}li.trace.collapsed>span.description:before{content:'\\25B9\\00A0';}li.funcall.collapsed>ol,li.trace.collapsed>ol{display:none;}";
    QString script = "function toggleBytecodes(){bytecodes=document.querySelectorAll('li.bytecode'); for(var i=0; i<bytecodes.length; i++){bytecodes[i].classList.toggle('hidden');}}";
    script += " function toggleClicksOnly(){boringtraces=document.querySelectorAll('li.trace:not(.click)'); for(var i=0; i<boringtraces.length; i++){boringtraces[i].classList.toggle('hidden');}}";
    script += " window.onload = function(){elems = document.querySelectorAll('li.funcall>span.itemname, li.trace>span.description'); for(var i=0; i<elems.length; i++){elems[i].onclick = function(){this.parentNode.classList.toggle('collapsed');}}};";

    QString res = "<html>\n<head>\n\t<meta charset=\"utf-8\"/>\n\t<title>Path Trace</title>\n\t<style type=\"text/css\">" + style + "</style>\n\t<script type=\"text/javascript\">" + script + "</script>\n</head>\n<body>\n";

    res += "<h1>Path Tracer Results</h1>\n";

    res += "<hr>\n<h3>Display Options:</h3>\n<ul class=\"controls\">\n";
    if(mReportBytecode){
        res += "\t<li><a onclick=\"toggleBytecodes()\">Toggle Bytecodes</a></li>\n";
    }else{
        res += "\t<li>(Bytecode disabled)</li>\n";
    }
    res += "\t<li><a onclick=\"toggleClicksOnly()\">Toggle displaying click traces only</a></li>\n";
    res += "</ul>\n<hr>\n\n";

    if(mTraces.isEmpty()){
        res += "<p>No traces were recorded.</p>\n";
    }else{
        res += "<ol class=\"tracelist\" >\n";
        foreach(trace, mTraces){

            traceClass = trace.type == PAGELOAD ? "pageload" : (trace.type == CLICK ? "click" : "other");
            res += "\t<li class=\"trace "+traceClass+"\">\n\t\t<span class=\"label\">Trace Start:</span> <span class=\"description\">" + trace.description + "</span>\n\t\t<ol class=\"singletrace\">\n";
            indentLevel = 3;

            QListIterator<TraceItem> itemIt(trace.items);
            while(itemIt.hasNext()){
                item = itemIt.next();

                itemStr = item.name;
                itemStr.replace('&',"&amp;").replace('>',"&gt;").replace('<',"&lt;");
                itemStr = "<span class=\"itemname\">" + itemStr + "</span>";
                extraStr = item.message.isEmpty() ? "" : (" <span class=\"extrainfo\">" + item.message + "</span>");
                indent = QString(indentLevel, '\t');
                res += indent;

                switch(item.type){
                case FUNCALL:
                    // Peek ahead in the trace to find the unique id of the following bytecode. This provides a link to this function in the coverage report.
                    functionLink = "Could not find link to coverage report";
                    if(itemIt.hasNext()){
                        peek = itemIt.peekNext();
                        if(peek.type == BYTECODE){
                            functionLink = QString("%1-%2").arg(CodeBlockInfo::getId(peek.sourceOffset, peek.sourceUrl, peek.sourceStartLine)).arg(peek.bytecodeOffset); // This is the bytecode-id.
                            functionLink = "<a href=\"#" + functionLink + "\" onclick=\"alert('Bytecode ID is " + functionLink + "');return false;\">View Code</a>";
                        }
                    }
                    extraStr = QString("<span class=\"extrainfo\">File: <a href=\"%1\">%2</a>, Line: %3, %4</span>").arg(item.sourceUrl.toString()).arg(displayedUrl(item.sourceUrl, true)).arg(item.lineInFile).arg(functionLink);
                    res += "<li class=\"funcall\">\n"+indent+"\t<span class=\"label\">Function Call:</span> " + itemStr + extraStr + "\n"+indent+"\t<ol class=\"functionbody\">\n";
                    indentLevel++;
                    break;
                case FUNRET:
                    res += "</ol>\n" + QString(indentLevel-1, '\t') + "</li>\n";
                    indentLevel--;
                    break;
                case BYTECODE:
                    if(mReportBytecode){
                        res += "<li class=\"bytecode hidden\">" + itemStr + extraStr + "</li>\n";
                    }
                    break;
                case ALERT:
                    res += "<li class=\"alert\"><span class=\"label\">Alert Call:</span> " + itemStr + extraStr + "</li>\n";
                    break;
                default:
                    res += "<li class=\"unknown\"><span class=\"label\">Unknown:</span> " + itemStr + extraStr + "</li>\n";
                    break;
                }
            }

            res += "\t\t</ol>\n\t</li>\n";
        }
    res += "</ol>\n";
    }

    res += "</body>\n</html>\n";

    QString pathToFile = QString("traces-") + QDateTime::currentDateTime().toString("dd-MM-yy-hh-mm-ss") + ".html";
    writeStringToFile(pathToFile, res);
}

QString PathTracer::displayedUrl(QUrl url, bool fileNameOnly)
{
    QString name = url.toString(QUrl::RemoveQuery);
    if(fileNameOnly){
        name = name.split("/").last();
    }
    if(url.hasQuery()){
        name += "?...";
    }
    return name;
    // TODO: sometimes returns empty
}

QString PathTracer::displayedFunctionName(QString name)
{
    return name.isEmpty() ? "<no name>" : (name + "()");
}

}
