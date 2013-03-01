
#include <assert.h>

#include "coverageprioritizer.h"

namespace artemis
{

CoveragePrioritizer::CoveragePrioritizer() : PrioritizerStrategy(NULL)
{
}

double CoveragePrioritizer::prioritize(QSharedPointer<const ExecutableConfiguration> configuration,
                                       QSharedPointer<const ExecutionResult>,
                                       const AppModelPtr appmodel)
{
    float coverage = 1;

    foreach(QSharedPointer<const BaseInput> input, configuration->getInputSequence()->toList()) {
        coverage = coverage * appmodel->getCoverageListener()->getBytecodeCoverage(input);
    }

    assert(coverage >= 0 && coverage <= 1);

    return 1 - coverage;
}

void CoveragePrioritizer::reprioritize(WorkListPtr)
{

}

}
