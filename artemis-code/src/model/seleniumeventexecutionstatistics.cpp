#include "seleniumeventexecutionstatistics.h"

#include <QDebug>
#include "util/fileutil.h"
#include "runtime/input/events/keyboardeventparameters.h"
#include "runtime/input/events/mouseeventparameters.h"

namespace artemis{

    SeleniumEventExecutionStatistics::SeleniumEventExecutionStatistics(const QUrl& url){
        mUrl = url;
        init = false;
        qDebug() << "SELENIUM: initializing stats with url: " <<  url;
    }

    void SeleniumEventExecutionStatistics::registerEvent(EventTuple desc){
        qDebug() << "SELENIUM: Event description registered at: " << desc.mEventHandler->xPathToElement();
        mCurrentRegisteredHandlers.append(desc);
    }

    void SeleniumEventExecutionStatistics::beginNewIteration(){
        qDebug() << "SELENIUM: Begin new selenium iteration.";
        if(init){
            mRegisteredHandlers.append(mCurrentRegisteredHandlers);
        }
        init = true;
        mCurrentRegisteredHandlers = QList<EventTuple>();
    }

    void SeleniumEventExecutionStatistics::generateOutput(){
        beginNewIteration();
        qDebug() << "SELENIUM: Generating selenium output.";
        QList<SeleniumTableRow> rows;

        int i = 0;
        QMap<QString, QString> testNameToFile;
        QDir outDir = uniqueDir("selenium-");
        foreach(QList<EventTuple> list, mRegisteredHandlers){
            rows.append(SeleniumTableRow("open", mUrl.toString()));
            MouseEventParameters mep;
            KeyboardEventParameters kep;
            foreach(EventTuple desc, list){

                if(mep = dynamic_cast<MouseEventParameters>(desc.mEvtParams)){

                    if(mep.altKey){
                        rows.append(SeleniumTableRow("altKeyDown"));
                    }
                    if(mep.ctrlKey){
                        rows.append(SeleniumTableRow("controlKeyDown"));
                    }
                    if(mep.shiftKey){
                        rows.append(SeleniumTableRow("shiftKeyDown"));
                    }
                    if(mep.metaKey){
                        rows.append(SeleniumTableRow("metaKeyDown"));
                    }

                } else if(kep = dynamic_cast<KeyboardEventParameters>(desc.mEvtParams)){

                } else {
                    // Handle blur and stuff
                }

                //                rows.append(SeleniumTableRow(desc.mEventHandler->getName(), desc.mEventHandler->xPathToElement()));
                qDebug() << "SELENIUM: Adding row "<< desc.mEventHandler->getName() << desc.mEventHandler->xPathToElement();
                //TODO: Need better way of creating rows:
                //      Should support:
                //        * blur ect. http://natzp.blogspot.dk/2011/04/to-automate-on-blur-on-key-elements.html
                //        * ctrl, shift, .. keys on both keydown and mouse events
                //        * sending value on keydown
            }
            QString testName = "iteration";
            testName.append(QString::number(i));
            testNameToFile.insert(testName, createTestFile(outDir, testName , rows));
            rows = QList<SeleniumTableRow>();
            i ++;
        }
        createSuite(outDir, testNameToFile);


    }


    QString SeleniumEventExecutionStatistics::createTestFile(QDir dir, QString testName, QList<SeleniumTableRow> rows){
        QString fileName = QString(testName).append(".html");
        qDebug() << "SELENIUM: creating testfile with name" << testName << "and filename"<< fileName;

        QString rowString;

        foreach(SeleniumTableRow row, rows){


            rowString.append(
                        "<tr>"
                        "<td>").append(row.mEventName).append("</td>"
                             "<td>").append(row.mXPath).append("</td>"
                             "<td>").append(row.mValue).append("</td>"
                         "</tr>");
        }

        QString out =
                QString::fromStdString("<?xml version=\"1.0\" encoding=\"UTF-8\"?>"
                "<!DOCTYPE html PUBLIC \"-//W3C//DTD XHTML 1.0 Strict//EN\" \"http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd\">"
                "<html xmlns=\"http://www.w3.org/1999/xhtml\" xml:lang=\"en\" lang=\"en\">"
                "<head profile=\"http://selenium-ide.openqa.org/profiles/test-case\">"
                "<meta http-equiv=\"Content-Type\" content=\"text/html; charset=UTF-8\" />"
                "<link rel=\"selenium.base\" href=\"http://code.google.com/\" />"
                "<title>").append(testName).append("</title>"
                "</head>"
                "<body>"
                "<table cellpadding=\"1\" cellspacing=\"1\" border=\"1\">"
                "<thead>"
                "<tr><td rowspan=\"1\" colspan=\"3\">").append(testName).append("</td></tr>"
                "</thead><tbody>").append(rowString).append( "</tbody></table>"
                "</body>"
                "</html>");
        writeStringToFile(QString(dir.absoluteFilePath(fileName)), out);
        return fileName;
    }

    void SeleniumEventExecutionStatistics::createSuite(QDir dir, QMap<QString, QString> testNames){
        QString fileName = "seleniumSuite.html";
        qDebug() << "SELENIUM: creating testsuite";

        QString testsString;

        foreach (QString k, testNames.keys()){
             testsString.append("<tr><td><a href=\"").append(testNames.value(k)).append("\">").append(k).append("</a></td></tr>");
        }
        QString out = QString::fromStdString(
                "<?xml version=\"1.0\" encoding=\"UTF-8\"?>"
                "<!DOCTYPE html PUBLIC \"-//W3C//DTD XHTML 1.0 Strict//EN\" \"http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd\">"
                "<html xmlns=\"http://www.w3.org/1999/xhtml\" xml:lang=\"en\" lang=\"en\">"
                "<head>"
                  "<meta content=\"text/html; charset=UTF-8\" http-equiv=\"content-type\" />"
                  "<title>Test Suite</title>"
                "</head>"
                "<body>"
                "<table id=\"suiteTable\" cellpadding=\"1\" cellspacing=\"1\" border=\"1\" class=\"selenium\"><tbody>"
                "<tr><td><b>Test Suite</b></td></tr>").append(testsString).append("</tbody></table>"
                "</body>"
                "</html>");
        writeStringToFile(dir.absoluteFilePath(fileName),out);
    }

    QDir SeleniumEventExecutionStatistics::uniqueDir(QString name){
        int i = 0;
        QString finalName;
        while(QDir(finalName = QString(name).append(QString::number(i))).exists()){
            i ++;
        }
        QDir().mkdir(finalName);
        return QDir(finalName);

    }

}
