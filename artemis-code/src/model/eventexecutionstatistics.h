#ifndef EVENTEXECUTIONSTATISTICS_H
#define EVENTEXECUTIONSTATISTICS_H

#include "runtime/input/events/eventhandlerdescriptor.h"
#include "runtime/input/events/eventparameters.h"
#include <QString>

namespace artemis{

struct EventTuple{
    EventHandlerDescriptorConstPtr mEventHandler;
    EventParametersConstPtr mEvtParams;
    EventTuple(QSharedPointer<const EventHandlerDescriptor> eventHandler, QSharedPointer<const EventParameters> evtParams){
        mEventHandler = eventHandler;
        mEvtParams = evtParams;
    }
};

class EventExecutionStatistics
{
public:
    EventExecutionStatistics(){

    }

    virtual void registerEvent(EventTuple desc) = 0;

    virtual void beginNewIteration() = 0;

    virtual void generateOutput() = 0;
};


}
#endif // EVENTEXECUTIONSTATISTICS_H
