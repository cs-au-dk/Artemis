
#include <iostream>

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

    float pri = float(properitesWrittenBeforeLast.intersect(propertiesReadByLast).size() + 1) / float(propertiesReadByLast.size() + 1);

    /*std::cout << configuration->toString().toStdString() << std::endl;
    std::cout << "PRIORITY = " << pri << " " \
              << "with propertiesReadByLast = " << propertiesReadByLast.size() << " and properitesWrittenBeforeLast = " << properitesWrittenBeforeLast.size() << std::endl;
    foreach (QString prop, properitesWrittenBeforeLast.toList()) {
        std::cout << "W: " << prop.toStdString() << std::endl;
    }
    foreach (QString prop, propertiesReadByLast.toList()) {
        std::cout << "R: " << prop.toStdString() << std::endl;
    }*/

    return pri;
}

void ReadWritePrioritizer::reprioritize(WorkListPtr)
{

}

}
