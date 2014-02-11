#ifndef STUBEVENTEXECUTIONSTATISTICS_H
#define STUBEVENTEXECUTIONSTATISTICS_H

#include "eventexecutionstatistics.h"

namespace artemis{

class StubEventExecutionStatistics: public EventExecutionStatistics
{
public:
    StubEventExecutionStatistics(){}

    void registerEventDescription(EventHandlerDescriptorConstPtr desc);

    void beginNewIteration();

    void generateOutput();
};

}

#endif // STUBEVENTEXECUTIONSTATISTICS_H
