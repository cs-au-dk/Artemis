#ifndef SELENIUMEVENTEXECUTIONSTATISTICS_H
#define SELENIUMEVENTEXECUTIONSTATISTICS_H

#include "eventexecutionstatistics.h"

#include <QList>

namespace artemis{

struct SeleniumTableRow{
    QString mEventName, mXPath;

    SeleniumTableRow(QString eventName, QString xPath){
        mEventName = eventName;
        mXPath = xPath;
    }

};

class SeleniumEventExecutionStatistics : public EventExecutionStatistics
{
public:
    SeleniumEventExecutionStatistics(const QUrl& url);

    void registerEventDescription(EventHandlerDescriptorConstPtr desc);

    void beginNewIteration();

    void generateOutput();

protected:
    QList<QList<EventHandlerDescriptorConstPtr> > mRegisteredHandlers;
    QList<EventHandlerDescriptorConstPtr> *mCurrentRegisteredHandlers;
    QUrl mUrl;


private:
    void createSuite(QMap<QString, QString> testNames);
    void createTestFile(QString testName, QList<SeleniumTableRow> rows);

};
}
#endif // SELENIUMEVENTEXECUTIONSTATISTICS_H
