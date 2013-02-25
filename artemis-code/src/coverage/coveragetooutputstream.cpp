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
#include "coveragetooutputstream.h"

#include <QTextStream>
#include <QDebug>
#include "util/loggingutil.h"
#include <math.h>

namespace artemis
{

void writeCoverageReport(const CodeCoverage& cov)
{
    float totalPct = 0;
    int numFiles = 0 ;
    foreach(int id, cov.sourceIds()) {
        const SourceInfo* info = cov.sourceInfo(id);
        QString src = info->source();
        QTextStream read(&src);
        qDebug() << "Coverage for source located at URL: " << info->url().toString() << "  line " << info->startLine();
        QMap<int, LineInfo> li = cov.lineInfo(id);
        int i = info->startLine();
        int numExecutedLines = 0;
        while (!read.atEnd()) {
            LineInfo curr = li[i++];
            QString prefix;

            if (curr.isExecuted()) {
                prefix = ">>>";
                numExecutedLines++;
            }
            else {
                prefix = "   ";
            }

            QString line = prefix + read.readLine() + "\n";
            qDebug() << line;
        }

        float pct = ((numExecutedLines+0.0)/(li.size()+0.0))*100;
        qDebug() << "Executed "<<QString::number(numExecutedLines)<<" lines of "<<QString::number(li.size())<<" lines ("<<QString::number(floor(pct))<<"%).\n\n";
        numFiles++;
        totalPct += pct;
    }
    QString pctString = "Executed ";
    pctString += QString::number(floor(totalPct/(numFiles+0.0)));
    pctString += "% of ";
    pctString += QString::number(numFiles);
    pctString += " files.";

    Log::info(pctString.toStdString());

}
}
