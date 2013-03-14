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
#ifndef ARTEMISOPTIONS_H
#define ARTEMISOPTIONS_H

#include <QObject>
#include <QUrl>
#include <QSettings>

#include "runtime/worklist/worklist.h"
#include "strategies/termination/terminationstrategy.h"
#include "strategies/prioritizer/prioritizerstrategy.h"
#include "strategies/inputgenerator/targets/targetdescriptor.h"
#include "runtime/input/events/eventhandlerdescriptor.h"
#include "strategies/inputgenerator/targets/jquerylistener.h"

namespace artemis
{

enum FormInputGenerationStrategies {
    Random, ConstantString
};

enum PrioritizerStrategies {
    CONSTANT, RANDOM, COVERAGE, READWRITE, ALL_STRATEGIES
};

enum CoverageReport {
    STDOUT, HTML, NONE
};

enum MajorMode {
    AUTOMATED, MANUAL
};

typedef struct OptionsType {

    OptionsType() :
        iterationLimit(1),
        numberSameLength(1),
        recreatePage(false),
        disableStateCheck(true),
        formInputGenerationStrategy(Random),
        prioritizerStrategy(CONSTANT),
        outputCoverage(NONE),
        majorMode(AUTOMATED)
    {}

    QMap<QString, QString> presetFormfields;
    QMap<QString, QString> presetCookies;

    QSet<QUrl> coverageIgnoreUrls;

    int iterationLimit;
    int numberSameLength;

    bool recreatePage;
    bool disableStateCheck;

    QString useProxy;
    QString dumpPageStates;

    FormInputGenerationStrategies formInputGenerationStrategy;
    PrioritizerStrategies prioritizerStrategy;
    CoverageReport outputCoverage;

    MajorMode majorMode;

} Options;

}
#endif // ARTEMISOPTIONS_H
