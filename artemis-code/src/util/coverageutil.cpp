#include "coverageutil.h"
#include "fileutil.h"
#include <QTextDocument>
#include <QStringList>


namespace artemis {
void write_coverage_html(QString filename, CodeCoverage cc){
    QString res = "<html><head><meta charset=\"utf-8\"/><title>Test</title></head><body><style>";
    res += "table { border-collapse: collapse; } td.covered { background-color: #00FF00; } td.uncovered { background-color: #FF0000; }</style>";
    foreach (int p, cc.source_ids()) {
        res += "<h2>" + Qt::escape(cc.source_info(p).getURL()) + "</h2>";
        res += "<pre><table>";

        int startline = cc.source_info(p).getStartLine();
        foreach (QString line, cc.source_info(p).getSource().split("\n", QString::KeepEmptyParts)) {
            res += "<tr><td>" + QString::number(startline) + "</td><td class=\""
                    + (cc.line_info(p).contains(startline) ? "covered" : "uncovered")
                    + "\">" + QTextDocument(line).toHtml() + "</td></tr>";
            startline += 1;
        }
        res += "</table></pre>";

    }
    res += ("</body></html>");
    write_string_to_file("coverage.html", res);

}
}

