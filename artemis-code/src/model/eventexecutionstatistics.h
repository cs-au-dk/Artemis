#ifndef EVENTEXECUTIONSTATISTICS_H
#define EVENTEXECUTIONSTATISTICS_H

#include "runtime/input/events/eventhandlerdescriptor.h"
#include <QString>

namespace artemis{

class EventExecutionStatistics
{
public:
    EventExecutionStatistics(){

    }

    virtual void registerEventDescription(EventHandlerDescriptorConstPtr desc) = 0;

    virtual void beginNewIteration() = 0;

    virtual QString generateOutput() = 0;
};


}
#endif // EVENTEXECUTIONSTATISTICS_H
