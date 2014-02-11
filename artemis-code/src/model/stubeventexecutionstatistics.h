#ifndef STUBEVENTEXECUTIONSTATISTICS_H
#define STUBEVENTEXECUTIONSTATISTICS_H

#include "eventexecutionstatistics.h"

namespace artemis{

class StubEventExecutionStatistics: public EventExecutionStatistics
{
public:
    StubEventExecutionStatistics(){}

    virtual void registerEvent(EventTuple desc);

    void beginNewIteration();

    void generateOutput();
};

}

#endif // STUBEVENTEXECUTIONSTATISTICS_H
