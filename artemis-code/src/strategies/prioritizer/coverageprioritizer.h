#ifndef COVERAGEPRIORITIZER_H
#define COVERAGEPRIORITIZER_H

#include "prioritizerstrategy.h"

namespace artemis
{

class CoveragePrioritizer : public PrioritizerStrategy
{

public:
    CoveragePrioritizer();

    double prioritize(QSharedPointer<const ExecutableConfiguration> newConf, AppModelConstPtr);

};

}

#endif // COVERAGEPRIORITIZER_H
