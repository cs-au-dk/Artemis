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

        int i = 1;
        QMap<QString, QString> testNameToFile;
        QDir outDir = uniqueDir("selenium-");
        foreach(QList<EventTuple> list, mRegisteredHandlers){
            rows.append(SeleniumTableRow("open", mUrl.toString()));
            foreach(EventTuple desc, list){
                QSharedPointer<const MouseEventParameters> mep = qSharedPointerDynamicCast<const MouseEventParameters>(desc.mEvtParams);
                QSharedPointer<const KeyboardEventParameters> kep = qSharedPointerDynamicCast<const KeyboardEventParameters>(desc.mEvtParams);

                if(mep){

                    if(mep->altKey){
                        rows.append(SeleniumTableRow("altKeyDown"));
                    }
                    if(mep->ctrlKey){
                        rows.append(SeleniumTableRow("controlKeyDown"));
                    }
                    if(mep->shiftKey){
                        rows.append(SeleniumTableRow("shiftKeyDown"));
                    }
                    if(mep->metaKey){
                        rows.append(SeleniumTableRow("metaKeyDown"));
                    }

                    rows.append(SeleniumTableRow(desc.mEventHandler->getName(), desc.mEventHandler->xPathToElement()));


                    if(mep->metaKey){
                        rows.append(SeleniumTableRow("metaKeyUp"));
                    }
                    if(mep->altKey){
                        rows.append(SeleniumTableRow("altKeyUp"));
                    }
                    if(mep->ctrlKey){
                        rows.append(SeleniumTableRow("controlKeyUp"));
                    }
                    if(mep->shiftKey){
                        rows.append(SeleniumTableRow("shiftKeyUp"));
                    }

                } else if(kep){
                    if(kep->altKey){
                        rows.append(SeleniumTableRow("altKeyDown"));
                    }
                    if(kep->ctrlKey){
                        rows.append(SeleniumTableRow("controlKeyDown"));
                    }
                    if(kep->shiftKey){
                        rows.append(SeleniumTableRow("shiftKeyDown"));
                    }
                    if(kep->metaKey){
                        rows.append(SeleniumTableRow("metaKeyDown"));
                    }

                    rows.append(SeleniumTableRow(desc.mEventHandler->getName(), desc.mEventHandler->xPathToElement(), kep->keyIdentifier));


                    if(kep->metaKey){
                        rows.append(SeleniumTableRow("metaKeyUp"));
                    }
                    if(kep->altKey){
                        rows.append(SeleniumTableRow("altKeyUp"));
                    }
                    if(kep->ctrlKey){
                        rows.append(SeleniumTableRow("controlKeyUp"));
                    }
                    if(kep->shiftKey){
                        rows.append(SeleniumTableRow("shiftKeyUp"));
                    }

                } else {
                    rows.append(SeleniumTableRow("fireEvent", desc.mEventHandler->xPathToElement(), desc.mEventHandler->getName()));
                }
            }
            QString testName = "iteration";
            int j = (int)mRegisteredHandlers.size()/10;
            while(j > (int)i/10){
                testName.append("0");
                j = (int)j/10;
            }
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
