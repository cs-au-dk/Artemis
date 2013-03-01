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
#include "coveragetooutputstream.h"

#include <inttypes.h>

#include <QTextStream>
#include <QDebug>
#include <QTextDocument>
#include <QStringList>
#include <QDir>
#include <QDateTime>

#include "util/fileutil.h"

#include "coveragetooutputstream.h"
#include "util/loggingutil.h"
#include <math.h>

namespace artemis
{

void writeCoverageStdout(CoverageListenerPtr cov)
{
    Log::info("=== Coverage information for execution ===");

    foreach(int sourceID, cov->getSourceIDs()) {

        const SourceInfo* sourceInfo = cov->getSourceInfo(sourceID);

        Log::info(QString("Coverage for source located at URL: " + sourceInfo->getURL() + "  line " + sourceInfo->getStartLine()).toStdString());

        QString src = sourceInfo->getSource();
        QTextStream read(&src);

        QSet<int> lineCoverage = cov->getLineCoverage(sourceID);
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

    QString res = "<html><head><meta charset=\"utf-8\"/><title>Test</title></head><body><style>";
    res += "table { border-collapse: collapse; } td.covered { background-color: #00FF00; } td.uncovered { background-color: #FF0000; }</style>";

    if (!existingFiles.isEmpty()) {
        res += "<a href=\"" + existingFiles.at(0) + "\">Previous run</a>";
    }

    foreach(int sourceID, cov->getSourceIDs()) {

        QSet<int> lineCoverage = cov->getLineCoverage(sourceID);

        res += "<h2>" + Qt::escape(cov->getSourceInfo(sourceID)->getURL()) + "</h2>";
        res += "<pre><table>";

        int startline = cov->getSourceInfo(sourceID)->getStartLine();
        foreach(QString line, cov->getSourceInfo(sourceID)->getSource().split("\n", QString::KeepEmptyParts)) {
            res += "<tr><td>" + QString::number(startline) + "</td><td class=\""
                   + QString(lineCoverage.contains(startline) ? "covered" : "uncovered")
                   + "\">" + QTextDocument(line).toHtml() + "</td></tr>";
            startline += 1;
        }
        res += "</table></pre>";

    }
    res += ("</body></html>");

    QString pathToFile = QString("coverage-") + QDateTime::currentDateTime().toString("dd-MM-yy-hh-mm-ss") + ".html";

    writeStringToFile(pathToFile, res);
}

}
