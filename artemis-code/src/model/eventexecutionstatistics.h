#ifndef EVENTEXECUTIONSTATISTICS_H
#define EVENTEXECUTIONSTATISTICS_H

#include "runtime/input/events/eventhandlerdescriptor.h"
#include "runtime/input/events/eventparameters.h"
#include "runtime/input/forms/forminputcollection.h"
#include <QString>

namespace artemis{

struct EventTuple{
    EventHandlerDescriptorConstPtr mEventHandler;
    EventParametersConstPtr mEvtParams;
    FormInputCollectionConstPtr mFormInput;
    EventTuple(QSharedPointer<const EventHandlerDescriptor> eventHandler, QSharedPointer<const EventParameters> evtParams, QSharedPointer<const FormInputCollection> formInput){
        mEventHandler = eventHandler;
        mEvtParams = evtParams;
        mFormInput = formInput;
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
