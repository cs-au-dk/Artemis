#ifndef COLLECTEDPRIORITIZER_H
#define COLLECTEDPRIORITIZER_H

#include "prioritizerstrategy.h"

namespace artemis
{

class CollectedPrioritizer : public PrioritizerStrategy
{
public:
    CollectedPrioritizer();
    double prioritize(QSharedPointer<const ExecutableConfiguration> newConf,
                      AppModelConstPtr);
    void addPrioritizer(PrioritizerStrategy* strategy);
private:
    list<PrioritizerStrategy*>* strategies;
};

}

#endif // COLLECTEDPRIORITIZER_H
