
#include <QSharedPointer>
#include <QList>
#include <QString>

#include "readwriteprioritizer.h"

namespace artemis
{

ReadWritePrioritizer::ReadWritePrioritizer() : PrioritizerStrategy(NULL)
{
}

double ReadWritePrioritizer::prioritize(QSharedPointer<const ExecutableConfiguration> configuration,
                                       QSharedPointer<const ExecutionResult>,
                                       const AppModelPtr appmodel)
{
    QList<QSharedPointer<const BaseInput> > inputSequence = configuration->getInputSequence()->toList();
    QSharedPointer<const BaseInput> last = inputSequence.last();
    inputSequence.removeLast();

    QSet<QString> propertiesReadByLast = appmodel->getJavascriptStatistics()->getPropertiesRead(last);
    QSet<QString> properitesWrittenBeforeLast;

    foreach(QSharedPointer<const BaseInput> input, inputSequence) {
        properitesWrittenBeforeLast.unite(appmodel->getJavascriptStatistics()->getPropertiesWritten(input));
    }

    return float(properitesWrittenBeforeLast.intersect(propertiesReadByLast).size() + 1) / float(propertiesReadByLast.size() + 1);

    //std::cout << "PRIORITY = " << pri << " " \
    //          << "with propertiesReadByLast = " << propertiesReadByLast.size() << " and properitesWrittenBeforeLast = " << properitesWrittenBeforeLast.size() << std::endl;
}

void ReadWritePrioritizer::reprioritize(WorkList*)
{

}

}
