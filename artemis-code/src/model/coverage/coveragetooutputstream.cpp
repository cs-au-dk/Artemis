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

void writeCoverageHtml(CoverageListenerPtr cov)
{

    QDir appdir("", "*.html", QDir::Time);
    QStringList existingFiles = appdir.entryList();
    QString timeString = QDateTime::currentDateTime().toString("dd-MM-yy-hh-mm-ss") ;
    QString res = "<html><head><meta charset=\"utf-8\"/><title>Coverage Report ("+timeString+")</title>";
    res += "\n";
    res += "<script type='text/javascript' src='https://google-code-prettify.googlecode.com/svn/loader/prettify.js'></script>";
    res += "\n";
    res += "<script src='http://code.jquery.com/jquery-latest.min.js'></script>";
    res += "\n";
    res += "<script type='text/javascript'> $.fn.updateOLOffset = function(){ if($(this).hasClass('startline')){var nr = $(this).attr('class').replace(/.*startlinenr\\[([0-9]+)\\].*/, '$1'); $(this).find('ol').attr('start',nr); $(this).removeClass('startline');}}; ";
    res += "$(document).ready(function(){  $('.expandLink').click(function(){  var pre = $(this).parent().find('pre');  var self = $(this); if(self.hasClass('expanded')){  pre.hide();  self.removeClass('expanded');  self.text('show code');} else {  pre.show();  if(!pre.hasClass('prettyprinted')){  pre.addClass('prettyprint');  prettyPrint(function(){  pre.removeClass('prettyprint');  pre.updateOLOffset();  });  }  self.addClass('expanded');  self.text('hide');  }  });});</script>";
    res += "\n";
    res += "<link rel='stylesheet' type='text/css' href='https://google-code-prettify.googlecode.com/svn/loader/prettify.css'>";
    res += "\n";
    res += "<style> .linenums > ol > li:nth-of-type(5n), .linenums > ol > li:nth-of-type(1) {list-style-type: decimal !important;} .linenums > ol > li {list-style-type: none;} pre {padding: 2px; border: 1px solid #888; display:none;} .expandLink{float:right;} pre > ol {overflow-x:auto;}</style>";
    res += "\n";
    res += "</head><body>";

    if (!existingFiles.isEmpty()) {
        res += "<a href=\"" + existingFiles.at(0) + "\">Previous run</a>";
    }

    foreach(int sourceID, cov->getSourceIDs()) {

        QSet<uint> lineCoverage = cov->getSourceInfo(sourceID)->getLineCoverage();
        res += "<div>";
        res += "<a href='#?' class='expandLink'>show</a>";
        res += "<h2>" + Qt::escape(cov->getSourceInfo(sourceID)->getURL()) + "</h2>";
        int startline = cov->getSourceInfo(sourceID)->getStartLine();
        res += "<pre class='linenums "+(startline >1 ? "startline startlinenr["+QString::number(startline)+"]":"")+"'>";

        foreach(QString line, cov->getSourceInfo(sourceID)->getSource().split("\n", QString::KeepEmptyParts)) {
            res += QTextDocument(line).toPlainText().replace("<","&lt;").replace(">","&gt;") + "&nbsp;\n";

        }
        res += "</pre></div>";

    }
    res += ("</body></html>");

    QString pathToFile = QString("coverage-") + timeString + ".html";

    writeStringToFile(pathToFile, res);
}

}
