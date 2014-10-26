/*
 * Copyright 2014 Aarhus University
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

#ifndef FASTTRACKINPUTGENERATOR_H
#define FASTTRACKINPUTGENERATOR_H

#include <QList>
#include <QSharedPointer>

#include "runtime/input/dominput.h"

#include "targets/targetgenerator.h"
#include "form/forminputgenerator.h"
#include "event/eventparametergenerator.h"
#include "model/eventexecutionstatistics.h"

#include "inputgeneratorstrategy.h"

namespace artemis
{

/**
 * @brief The FasttrackInputGenerator class
 *
 * This generator generates a single event sequence in which all known events (from the initial iteration) are triggered.
 * Thus, it fasttracks to an eventsequence which executes everything.
 *
 * This violates some Artemis assumptions, since we do not know if an event can be triggered since we do not know the state
 * after the first event we add to the event sequence. However, this should be seen as a quick and dirty way to quickly trigger
 * many events on a page, to do feature detection or something similar.
 *
 * The input generator will only generate a single event sequence!
 */
class FasttrackInputGenerator : public InputGeneratorStrategy
{
    Q_OBJECT

public:
    FasttrackInputGenerator(QObject* parent,
                         FormInputGeneratorConstPtr formInputGenerator,
                         EventParameterGeneratorConstPtr eventParameterInputGenerator,
                         TargetGeneratorConstPtr targetGenerator,
                         EventExecutionStatistics* execStat);

    QList<ExecutableConfigurationPtr> addNewConfigurations(ExecutableConfigurationConstPtr, ExecutionResultConstPtr);

private:
    FormInputGeneratorConstPtr mFormInputGenerator;
    EventParameterGeneratorConstPtr mEventParameterGenerator;
    TargetGeneratorConstPtr mTargetGenerator;
    EventExecutionStatistics* mExecStat;

};

}
#endif // FASTTRACKINPUTGENERATOR_H
