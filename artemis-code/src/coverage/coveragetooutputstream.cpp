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

void writeCoverageStdout(const CodeCoverage& cov)
{
    qDebug() << "=== Coverage information for execution ===";

    foreach(int id, cov.sourceIds()) {

        const SourceInfo* info = cov.sourceInfo(id);
        QString src = info->source();
        QTextStream read(&src);
        qDebug() << "Coverage for source located at URL: " << info->url().toString() << "  line " << info->startLine();
        QMap<int, LineInfo> li = cov.lineInfo(id);
        int i = info->startLine();

        while (!read.atEnd()) {
            LineInfo curr = li[i++];
            QString prefix;

            if (curr.isExecuted()) {
                prefix = ">>>";
            }
            else {
                prefix = "   ";
            }

            QString line = prefix + read.readLine() + "\n";
            qDebug() << line;
        }
    }
}

void writeCoverageHtml(CodeCoverage cc)
{

    QDir appdir("", "*.html", QDir::Time);
    QStringList existingFiles = appdir.entryList();

    QString res = "<html><head><meta charset=\"utf-8\"/><title>Test</title></head><body><style>";
    res += "table { border-collapse: collapse; } td.covered { background-color: #00FF00; } td.uncovered { background-color: #FF0000; }</style>";

    if (!existingFiles.isEmpty()) {
        res += "<a href=\"" + existingFiles.at(0) + "\">Previous run</a>";
    }

    foreach(int p, cc.sourceIds()) {
        res += "<h2>" + Qt::escape(cc.sourceInfo(p)->getURL()) + "</h2>";
        res += "<pre><table>";

        int startline = cc.sourceInfo(p)->getStartLine();
        foreach(QString line, cc.sourceInfo(p)->getSource().split("\n", QString::KeepEmptyParts)) {
            res += "<tr><td>" + QString::number(startline) + "</td><td class=\""
                   + (cc.lineInfo(p).contains(startline) ? "covered" : "uncovered")
                   + "\">" + QTextDocument(line).toHtml() + "</td></tr>";
            startline += 1;
        }
        res += "</table></pre>";

    }
    res += ("</body></html>");

    QString pathToFile = QDateTime::currentDateTime().toString("coverage-dd-MM-yy-hh-mm-ss") + ".html";

    writeStringToFile(pathToFile, res);
}

}
