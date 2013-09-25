/*
 * Copyright 2012 Aarhus University
 *
 * Licensed under the GNU General Public License, Version 3 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *          http://www.gnu.org/licenses/gpl-3.0.html
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
    if (configuration->isInitial()) {
        return 0;
    }

    QList<QSharedPointer<const BaseInput> > inputSequence = configuration->getInputSequence()->toList();
    QSharedPointer<const BaseInput> last = inputSequence.last();
    inputSequence.removeLast();

    QSet<QString> propertiesReadByLast = appmodel->getJavascriptStatistics()->getPropertiesRead(last);
    QSet<QString> properitesWrittenBeforeLast;

    foreach(QSharedPointer<const BaseInput> input, inputSequence) {
        properitesWrittenBeforeLast.unite(appmodel->getJavascriptStatistics()->getPropertiesWritten(input));
    }

    return float(properitesWrittenBeforeLast.intersect(propertiesReadByLast).size() + 1) / float(propertiesReadByLast.size() + 1);
}

}
