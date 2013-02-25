/*
  Copyright 2011 Simon Holm Jensen. All rights reserved.

  Redistribution and use in source and binary forms, with or without modification, are
  permitted provided that the following conditions are met:

     1. Redistributions of source code must retain the above copyright notice, this list of
        conditions and the following disclaimer.

     2. Redistributions in binary form must reproduce the above copyright notice, this list
        of conditions and the following disclaimer in the documentation and/or other materials
        provided with the distribution.

  THIS SOFTWARE IS PROVIDED BY SIMON HOLM JENSEN ``AS IS'' AND ANY EXPRESS OR IMPLIED
  WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND
  FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL <COPYRIGHT HOLDER> OR
  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
  CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
  SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
  ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
  NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
  ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

  The views and conclusions contained in the software and documentation are those of the
  authors and should not be interpreted as representing official policies, either expressed
  or implied, of Simon Holm Jensen
*/

#include <inttypes.h>

#include <QTextStream>
#include <QDebug>
#include <QTextDocument>
#include <QStringList>
#include <QDir>
#include <QDateTime>

#include "util/fileutil.h"

#include "coveragetooutputstream.h"

namespace artemis
{

void writeCoverageStdout(CoverageListener* cov)
{
    qDebug() << "=== Coverage information for execution ===";

    foreach(int sourceID, cov->getSourceIDs()) {

        const SourceInfo* sourceInfo = cov->getSourceInfo(sourceID);

        qDebug() << "Coverage for source located at URL: " << sourceInfo->getURL() << "  line " << sourceInfo->getStartLine();

        QString src = sourceInfo->getSource();
        QTextStream read(&src);

        QSet<int> lineCoverage = cov->getLineCoverage(sourceID);
        int lineNumber = sourceInfo->getStartLine();

        while (!read.atEnd()) {
            QString prefix = lineCoverage.contains(lineNumber) ? ">>>" : "   ";
            QString line = prefix + read.readLine() + "\n";
            qDebug() << line;
            lineNumber++;
        }
    }
}

void writeCoverageHtml(CoverageListener* cov)
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
