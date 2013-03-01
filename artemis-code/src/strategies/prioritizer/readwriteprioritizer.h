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
                      AppModelConstPtr);
};

}

#endif // READWRITEPRIORITIZER_H
