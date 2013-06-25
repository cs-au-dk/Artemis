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
    res += "<link rel='stylesheet' type='text/css' href='https://google-code-prettify.googlecode.com/svn/loader/prettify.css'>";
    res += "<style type='text/css'>*{margin:0;padding:0;font-family:Tahoma,Geneva,sans-serif;font-size:12pt;line-height:20px}body{padding:20px 0 70px 0}body>div>b{font-size:10pt}body>div{padding:20px;margin:10px 0}body>div:not(.info):not(#SymbolicNavigator):nth-of-type(2n+1){background:#eee}body>#SymbolicNavigator{position:fixed;bottom:0;background:#8e8e8e;margin:0;width:96%;height:50px;line-height:50px;padding:0 2%;color:#fff}body>#SymbolicNavigator a{color:#1d54aa;font-style:italic}body>div.info>.prev{display:block}h2{font-size:20pt;line-height:40px}h1{padding-left:20px;font-size:30pt;line-height:50px}.linenums>ol{padding-left:40px}.linenums>ol>li:nth-of-type(5n),.linenums>ol>li:nth-of-type(1){list-style-type:decimal!important}.linenums>ol>li{list-style-type:none;word-wrap:break-word}pre li:nth-of-type(2n){background:#eee}pre li:nth-of-type(2n+1){background:#fff}pre>ol>li.covered{background:#ffeeb2}pre>ol>li.symCovered{background:#e29c1d!important}pre>ol>li.linkedLine {background:#6f9!important}pre>ol>li.covered>span.covered,pre>ol>li.symCovered>span.covered{background:#ff6868}pre>ol>li.symCovered>span.symCovered,pre>ol>li.covered>span.symCovered{background:#ff004e}pre{padding:2px;border:1px solid #888;display:none}pre *{font-size:11pt}a{text-decoration:none}body>div>a.openLink{float:right;padding:0 10px;display:block;text-decoration:none}body>div>a.expandLink:visited{color:#fff}.arrow-right{width:0;height:0;border-top:5px solid transparent;border-bottom:5px solid transparent;border-left:5px solid darkblue}a.expandLink{display:block;font-size:10pt;text-align:center;background:#5a9dca;padding:3px;color:#fff;margin-top:5px;position:relative}a.expandLink:hover{background:#60acd8}a.expandLink.expanded{background:#e27171;box-shadow:0}a.openLink{background:#aaa;color:#fff;font-size:10pt;border-radius:2px}a.openLink:hover{background:#bbb}a.openLink .arrow-container{float:right;padding:5px 0;margin-left:10px}a.openLink .arrow-container .arrow-right{border-left-color:#fff}</style>";
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
    res += "<script type='text/javascript' >$.fn.updateOLOffset=function(){if($(this).hasClass(\"startline\")){var a=$(this).attr(\"class\").replace(/.*startlinenr\\[([0-9]+)\\].*/,\"$1\");$(this).find(\"ol\").attr(\"start\",a);$(this).removeClass(\"startline\")}};$.fn.updateOffset=function(){var b=$(this);if(b.size()>1){b.each(function(){$(this).updateOffset()});return}if(!b.hasClass(\"expanded\")){b.css(\"top\",\"\");return}var d=b.next(\"pre\");var a=d.offset();var c=(a.top-(b.outerHeight()))-($(window).scrollTop());b.css(\"top\",Math.max(0,Math.min(c*-1,d.outerHeight())))};$.fn.markLineCoverage=function(e,d){if(e==undefined){e=coverage}if(d==undefined){d=\"covered\"}var a=$(this);var g=a.parents(\"div\").attr(\"id\");var c,f=(c=a.find(\"ol.linenums\").first().attr(\"start\"))==undefined?1:c;var b=e[g];$.each(b,function(i,h){$(a.find(\"ol.linenums > li\").get(h-f)).addClass(d)})};$.fn.markRangeCoverage=function(e,c){var a=$(this);if(a.size()>1){a.each(function(g){g.markRangeCoverage()});return}if(e==undefined){e=coverageRange}if(c==undefined){c=\"covered\"}var f=a.parents(\"div\").attr(\"id\");var b=e[f];var d=function(i,g,h){var k=g+i.text().replace(\"&gt;\",\">\").replace(\"&lt;\",\"<\").replace(\"&amp;\",\"&\").length;var j=h[3]>=0?h[3]:k+1;if((h[1]<g&&j>g)||(h[1]<k&&j>k)){i.addClass(c)}return k};$.each(b,function(j,i){if(i.length!=4){return}var h=$(\"ol.linenums > li:eq(\"+(i[0]-1)+\")\",a),m=i[0]==i[2]?h:$(\"ol.linenums > li:eq(\"+(i[2]-1)+\")\",a);if(h==m){var g=0;h.children(\"span\").each(function(){g=d($(this),g,i)})}else{var g=0;h.children(\"span\").each(function(){g=d($(this),g,[i[0],i[1],i[2],-1])});g=0;m.children(\"span\").each(function(){g=d($(this),g,[i[0],0,i[2],i[3]])})}})};$.fn.toggleExpandCode=function(c){if(c==undefined){c=function(){}}var a=$(this);var b=a.parent().find(\"pre\");if(a.hasClass(\"expanded\")){b.hide();a.removeClass(\"expanded\");a.updateOffset();$(window).scrollTop(Math.min(a.offset().top,$(window).scrollTop()));a.text(\"show code coverage\")}else{b.show();if(!b.hasClass(\"prettyprinted\")){b.addClass(\"prettyprint\");prettyPrint(function(){b.removeClass(\"prettyprint\");b.updateOLOffset();b.markLineCoverage();b.markLineCoverage(symbolicCoverage,\"symCovered\");b.markRangeCoverage();b.markRangeCoverage(symbolicCoverageRange,\"symCovered\");c()})}else{c()}a.addClass(\"expanded\");a.text(\"hide\")}};$.fn.blinkLine=function(){var a=$(this);a.css(\"opacity\",0);a.animate({opacity:1},300)};$.fn.scrollToLine=function(){var a=(this);var d=a.offset().top;var c=$(window),b=c.scrollTop()+200;if(b>d||b+c.height()-400<d+a.outerHeight()){c.scrollTop(d-(c.height()-a.outerHeight())/2)}};function setUpSymbolicInfo(){var d=0,f=null;$.each(symbolicCoverage,function(h,g){d+=g.length});var c=$('<div id=\"SymbolicNavigator\">'+d+\" symbolic tainted lines found.</div>\");c.appendTo(\"body\");if(d>0){var e=function(m){m=(n=m%d)>=0?n:d+n;f=m;var l=$(\"div.code\");var p=null,k,h,n=k=0;while(p==null){p=$(l[n]).attr(\"id\");h=k;k+=symbolicCoverage[p].length;p=k>m?$(l[n]):null;n++}var g;var o=function(){var i=p.find(\"ol.linenums > li.symCovered:eq(\"+(m-h)+\")\");i.scrollToLine();i.blinkLine()};if(!(g=p.find(\"a.expandLink\")).hasClass(\"expanded\")){g.toggleExpandCode(o)}else{o()}};var a=$('<a href=\"#\">next line</a>'),b=$('<a href=\"#\">previous line</a> ');c.append(\" Go to \");c.append(b);c.append(\" - \");c.append(a);b.click(function(){e(f==null?0:f-1);return false});a.click(function(){e(f==null?0:f+1);return false})}}function linkToCode(){var e=window.location.search.substr(1).split(\"&\");var d=null;var a=null;for(var b=0;b<e.length;b++){var c=e[b].split(\"=\");if(c.length==2){if(c[0]==\"code\"){d=c[1]}else{if(c[0]==\"line\"){a=parseInt(c[1],10)}}}}if(d!==null&&a!==null){$(\"#\"+d).first().each(function(){$(\".expandLink\",this).first().toggleExpandCode();$(\"ol.linenums\",this).first().each(function(){var f;if($(this).attr(\"start\")===undefined){f=1}else{f=parseInt($(this).attr(\"start\"),10)}$(\"li\",this).eq(a-f).scrollToLine();$(\"li\",this).eq(a-f).blinkLine();$(\"li\",this).eq(a-f).addClass(\"linkedLine\")})})}}$(document).ready(function(){var a=function(){$(\".expandLink.expanded\").updateOffset()};$(window).scroll(a);$(window).resize(a);$(\".expandLink\").click(function(){$(this).toggleExpandCode();return false});setUpSymbolicInfo();linkToCode()});</script>";

    res += ("</body></html>");

    pathToFile = QString("coverage-") + timeString + ".html";

    writeStringToFile(pathToFile, res);
}

}
