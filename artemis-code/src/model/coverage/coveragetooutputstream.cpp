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

#include <inttypes.h>

#include <QTextStream>
#include <QDebug>
#include <QTextDocument>
#include <QStringList>
#include <QDir>
#include <QDateTime>
#include <math.h>

#include "util/fileutil.h"
#include "util/loggingutil.h"

#include "coveragetooutputstream.h"

namespace artemis
{

void writeCoverageStdout(CoverageListenerPtr cov)
{
    Log::info("=== Coverage information for execution ===");

    foreach(int sourceID, cov->getSourceIDs()) {

        const SourceInfoPtr sourceInfo = cov->getSourceInfo(sourceID);

        Log::info(QString("Coverage for source located at URL: " + sourceInfo->getURL() + "  line " + sourceInfo->getStartLine()).toStdString());

        QString src = sourceInfo->getSource();
        QTextStream read(&src);

        QSet<uint> lineCoverage = sourceInfo->getLineCoverage();
        int lineNumber = sourceInfo->getStartLine();

        while (!read.atEnd()) {
            QString prefix = lineCoverage.contains(lineNumber) ? ">>>" : "   ";
            QString line = prefix + read.readLine();
            Log::info(line.toStdString());
            lineNumber++;
        }
    }
}

QString generateRangeJSMapElement(int startline, int startchar, int endline, int endchar){
    QString ret = "";
    ret += "["+QString::number(startline)+", "+QString::number(startchar)+", "+QString::number(endline)+", "+QString::number(endchar)+"]";
    return ret;
}

QString generateLineCoverageJSListElements(QSet<uint> map){
    bool first = true;
    QString ret = "";
    foreach(uint i, map){
        if(!first){
            ret += ", ";
        }
        ret += QString::number(i);
        first = false;
    }
    return ret;
}

QString generateRangeCoverage(QList<int>& rangeKeys,QMap<int,int>& coverageRange , int& pendingEnd,int& pendingStartChar, int& pendingStartLine, int currentChar, int currentLine, int lineLength){
    QString coverageRangeString = "";
    if(pendingEnd > 0 && pendingEnd < currentChar+lineLength){
        coverageRangeString += generateRangeJSMapElement(pendingStartLine,pendingStartChar,currentLine,pendingEnd-currentChar) + ", ";
        pendingEnd = -1;
    }
    int key;
    while(!rangeKeys.isEmpty() && (key = rangeKeys.first()) < currentChar+lineLength){
        if(coverageRange[key] >= currentChar+lineLength){
            pendingEnd = coverageRange[key];
            pendingStartLine = currentLine;
            pendingStartChar = key - currentChar;
        } else {
            coverageRangeString += generateRangeJSMapElement(currentLine,key-currentChar,currentLine,coverageRange[key]-currentChar)+", ";
        }
        rangeKeys.removeFirst();
    }
    return coverageRangeString;
}

void writeCoverageHtml(CoverageListenerPtr cov, QString& pathToFile)
{

    QDir appdir("", "*.html", QDir::Time);
    QStringList existingFiles = appdir.entryList();
    QString timeString = QDateTime::currentDateTime().toString("dd-MM-yy-hh-mm-ss") ,
            timeString2 = QDateTime::currentDateTime().toString("dd-MM-yy hh:mm:ss") ;
    QString res = "<!DOCTYPE html>\n<html><head><meta charset=\"utf-8\"/><title>Coverage Report ("+timeString2+")</title>";
    res += "<script type='text/javascript' src='https://google-code-prettify.googlecode.com/svn/loader/prettify.js'></script>";
    res += "<script src='http://code.jquery.com/jquery-latest.min.js'></script>";
    res += "<script type='text/javascript' >function markLineNumbers(){$('.code').each(function(){code = $(this).attr('id'); $('ol.linenums', this).each(function(){ if($(this).attr('start') === undefined){num=1}else{num=parseInt($(this).attr('start'),10)} $('li', this).each(function(){$(this).attr('id', code + '-L' + num); num++ }) } ) }) }</script>";
    res += "<link rel='stylesheet' type='text/css' href='https://google-code-prettify.googlecode.com/svn/loader/prettify.css'>";
    res += "<style type='text/css'>*{margin:0;padding:0;font-family:Tahoma,Geneva,sans-serif;font-size:12pt;line-height:20px}body{padding:20px 0 70px 0}body>div>b{font-size:10pt}body>div{padding:20px;margin:10px 0}body>div:not(.info):not(#SymbolicNavigator):nth-of-type(2n+1){background:#eee}body>#SymbolicNavigator{position:fixed;bottom:0;background:#8e8e8e;margin:0;width:96%;height:50px;line-height:50px;padding:0 2%;color:#fff}body>#SymbolicNavigator a{color:#1d54aa;font-style:italic}body>div.info>.prev{display:block}h2{font-size:20pt;line-height:40px}h1{padding-left:20px;font-size:30pt;line-height:50px}.linenums>ol{padding-left:40px}.linenums>ol>li:nth-of-type(5n),.linenums>ol>li:nth-of-type(1){list-style-type:decimal!important}.linenums>ol>li{list-style-type:none;word-wrap:break-word}pre li:nth-of-type(2n){background:#eee}pre li:nth-of-type(2n+1){background:#fff}pre>ol>li.covered{background:#ffeeb2}pre>ol>li.symCovered{background:#e29c1d!important}pre>ol>li.covered>span.covered,pre>ol>li.symCovered>span.covered{background:#ff6868}pre>ol>li.symCovered>span.symCovered,pre>ol>li.covered>span.symCovered{background:#ff004e}pre{padding:2px;border:1px solid #888;display:none}pre *{font-size:11pt}a{text-decoration:none}body>div>a.openLink{float:right;padding:0 10px;display:block;text-decoration:none}body>div>a.expandLink:visited{color:#fff}.arrow-right{width:0;height:0;border-top:5px solid transparent;border-bottom:5px solid transparent;border-left:5px solid darkblue}a.expandLink{display:block;font-size:10pt;text-align:center;background:#5a9dca;padding:3px;color:#fff;margin-top:5px;position:relative}a.expandLink:hover{background:#60acd8}a.expandLink.expanded{background:#e27171;box-shadow:0}a.openLink{background:#aaa;color:#fff;font-size:10pt;border-radius:2px}a.openLink:hover{background:#bbb}a.openLink .arrow-container{float:right;padding:5px 0;margin-left:10px}a.openLink .arrow-container .arrow-right{border-left-color:#fff}</style>";
    res += "</head><body>";
    res += "<h1>Coverage Report</h1>";
    res += "<div class='info'>Ran: "+timeString+"<br /> Number of scripts: "+QString::number(cov->getSourceIDs().length());
    if (!existingFiles.isEmpty()) {
        res += "<a class='prev' href=\"" + existingFiles.at(0) + "\">Previous run</a>";
    }
    res += "</div>";
    QString coverageJSString = "", symbolicCoverageJSString = "", coverageRangeString = "", symbolicCoverageRangeString = "";
    bool first = true;
    foreach(uint sourceID, cov->getSourceIDs()) {

        QString url = Qt::escape(cov->getSourceInfo(sourceID)->getURL()).trimmed(), id = "ID"+QString::number(sourceID);

        res += "<div id='"+id+"' class='code'>";
        res += "<a href='"+url+"' target='_blank' class='openLink'><div class='arrow-container'><div class='arrow-right'>&nbsp;</div></div>Go to file</a>";

        int index = url.lastIndexOf("/");
        QString name, tail = name = url.right(url.size() - index - 1);
        name = name.left(name.indexOf("?")).left(name.indexOf("#"));
        tail = tail.right(tail.size()-name.size());

        res += "<b>"+ url.left(index+1) +"</b>";
        res += "<h2 "+(name.size()<=0?" class='inactive'> &lt;index file&gt; ":"> "+name )+"</h2>";
        res += tail.size()>0?"<b>"+tail+"</b>":"";
        res += "<a href='#?' class='expandLink'>show code coverage</a>";

        int startline = cov->getSourceInfo(sourceID)->getStartLine();
        res += "<pre class='linenums "+(startline >1 ? "startline startlinenr["+QString::number(startline)+"]":"")+"'>";

        int currentChar = 0, currentLine = 1;

        QMap<int,int> coverageRange = cov->getSourceInfo(sourceID)->getRangeCoverage(),
                symbolicCoverageRange = cov->getSourceInfo(sourceID)->getSymbolicRangeCoverage();

        QList<int> rangeKeys = coverageRange.keys(),
                symbolicRangeKeys = symbolicCoverageRange.keys();

        int pendingEnd = -1, pendingStartLine = -1, pendingStartChar = -1, sPendingEnd = -1, sPendingStartLine = -1, sPendingStartChar = -1;

        if(!first){
            coverageJSString += ", ";
            symbolicCoverageJSString += ", ";
            coverageRangeString += ", ";
            symbolicCoverageRangeString += ", ";
        }

        QString s = "\""+id+"\":[";

        coverageJSString += s + generateLineCoverageJSListElements( cov->getSourceInfo(sourceID)->getLineCoverage())+"]";
        symbolicCoverageJSString += s + generateLineCoverageJSListElements( cov->getSourceInfo(sourceID)->getSymbolicLineCoverage())+"]";

        coverageRangeString += s;
        symbolicCoverageRangeString += s;

        foreach(QString line, cov->getSourceInfo(sourceID)->getSource().split("\n", QString::KeepEmptyParts)) {

            int lineLength = line.length()+1;
            res += QTextDocument(line).toPlainText().replace("&","&amp;").replace("<","&lt;").replace(">","&gt;").replace(QRegExp("\\s*$"), "") + "&nbsp;\n";
            coverageRangeString += generateRangeCoverage(rangeKeys,coverageRange,pendingEnd,pendingStartChar,pendingStartLine, currentChar, currentLine,lineLength);
            symbolicCoverageRangeString += generateRangeCoverage(symbolicRangeKeys,symbolicCoverageRange,sPendingEnd,sPendingStartChar,sPendingStartLine,currentChar,currentLine,lineLength);
            currentChar += lineLength;
            currentLine ++;
        }

        coverageRangeString += "[]]";
        symbolicCoverageRangeString += "[]]";

        first = false;
        res += "</pre></div>";
    }

    res += "<script type='text/javascript'> var coverage = {" + coverageJSString + "}; var symbolicCoverage = {" + symbolicCoverageJSString + "}; var coverageRange = {"+coverageRangeString+"}; var symbolicCoverageRange = {"+symbolicCoverageRangeString+"}; </script>";
    res += "<script type='text/javascript' src='artemis-code/src/model/coverage/coveragehtml.js' ></script>"; // TEMP, will inline again once I've finished making chanegs.

    res += ("</body></html>");

    pathToFile = QString("coverage-") + timeString + ".html";

    writeStringToFile(pathToFile, res);
}

}
