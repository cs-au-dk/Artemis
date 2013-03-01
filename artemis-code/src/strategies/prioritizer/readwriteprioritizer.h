#ifndef READWRITEPRIORITIZER_H
#define READWRITEPRIORITIZER_H

#include "prioritizerstrategy.h"

namespace artemis
{

class ReadWritePrioritizer : public PrioritizerStrategy
{
public:
    ReadWritePrioritizer();

    double prioritize(QSharedPointer<const ExecutableConfiguration> newConf,
                      QSharedPointer<const ExecutionResult> result,
                      const AppModelPtr);

    void reprioritize(WorkListPtr worklist);
};

}

#endif // READWRITEPRIORITIZER_H
