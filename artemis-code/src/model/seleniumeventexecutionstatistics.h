#ifndef SELENIUMEVENTEXECUTIONSTATISTICS_H
#define SELENIUMEVENTEXECUTIONSTATISTICS_H

#include "eventexecutionstatistics.h"

#include <QList>
#include <QString>
#include <QDir>

namespace artemis{

struct SeleniumTableRow{
    QString mEventName, mXPath, mValue;

    SeleniumTableRow(QString eventName){
        mEventName = eventName;
    }


    SeleniumTableRow(QString eventName, QString xPath){
        mEventName = eventName;
        mXPath = xPath;
    }
    SeleniumTableRow(QString eventName, QString xPath, QString value){
        mEventName = eventName;
        mXPath = xPath;
        mValue = value;
    }

};

class SeleniumEventExecutionStatistics : public EventExecutionStatistics
{
public:
    SeleniumEventExecutionStatistics(const QUrl& url);

    virtual void registerEvent(EventTuple desc);

    void beginNewIteration();

    void generateOutput();

protected:
    QList<QList<EventTuple> > mRegisteredHandlers;
    QList<EventTuple> mCurrentRegisteredHandlers;
    QUrl mUrl;


private:
    void createSuite(QDir dir, QMap<QString, QString> testNames);
    QString createTestFile(QDir dir, QString testName, QList<SeleniumTableRow> rows);
    QDir uniqueDir(QString name);
    bool init;
};
}
#endif // SELENIUMEVENTEXECUTIONSTATISTICS_H
