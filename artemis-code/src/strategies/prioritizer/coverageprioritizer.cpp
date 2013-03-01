
#include <assert.h>

#include "coverageprioritizer.h"

namespace artemis
{

CoveragePrioritizer::CoveragePrioritizer() :
    PrioritizerStrategy()
{
}

double CoveragePrioritizer::prioritize(ExecutableConfigurationConstPtr configuration,
                                       AppModelConstPtr appmodel)
{
    float coverage = 1;

    foreach(QSharedPointer<const BaseInput> input, configuration->getInputSequence()->toList()) {
        coverage = coverage * appmodel->getCoverageListener()->getBytecodeCoverage(input);
    }

    assert(coverage >= 0 && coverage <= 1);

    return 1 - coverage;
}

}
