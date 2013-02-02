#include "coverageutil.h"
#include "fileutil.h"
#include <QTextDocument>
#include <QStringList>
#include <QDir>
#include <QDateTime>

namespace artemis
{

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

    QString pathToFile = QDateTime::currentDateTime().toString("dd-MM-yy-hh-mm-ss") + ".html";

    writeStringToFile(pathToFile, res);
}

}

