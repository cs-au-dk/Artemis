#ifndef SELENIUMEVENTEXECUTIONSTATISTICS_H
#define SELENIUMEVENTEXECUTIONSTATISTICS_H

#include "eventexecutionstatistics.h"

#include <QList>

namespace artemis{
class SeleniumEventExecutionStatistics : public EventExecutionStatistics
{
public:
    SeleniumEventExecutionStatistics(){

    }

    void registerEventDescription(EventHandlerDescriptorConstPtr desc);

    void beginNewIteration();

    QString generateOutput();

protected:
    QList<EventHandlerDescriptorConstPtr> mRegisteredHandlers;
};
}
#endif // SELENIUMEVENTEXECUTIONSTATISTICS_H
