#ifndef JSONEVENTEXECUTIONSTATISTICS_H
#define JSONEVENTEXECUTIONSTATISTICS_H

#include "eventexecutionstatistics.h"

namespace artemis {

class JSONEventExecutionStatistics : public EventExecutionStatistics
{
public:
    JSONEventExecutionStatistics(const QUrl& url);

    virtual void registerEvent(EventTuple desc);

    void beginNewIteration();

    void generateOutput();

protected:
    QList<QList<EventTuple> > mRegisteredHandlers;
    QList<EventTuple> mCurrentRegisteredHandlers;
    QUrl mUrl;


private:
    bool init;
    QString eventTupleToJSONString(EventTuple evt);
};
}
#endif // JSONEVENTEXECUTIONSTATISTICS_H
