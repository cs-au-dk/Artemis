/*
 * Copyright 2012 Aarhus University
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
#include <iostream>

#include <QSharedPointer>
#include <QList>
#include <QString>

#include "readwriteprioritizer.h"

namespace artemis
{

ReadWritePrioritizer::ReadWritePrioritizer() : PrioritizerStrategy()
{
}

double ReadWritePrioritizer::prioritize(QSharedPointer<const ExecutableConfiguration> configuration,
                                        AppModelConstPtr appmodel)
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

}
