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

#include <QUrl>
#include <QSet>
#include <QMap>
#include <QString>

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
    AUTOMATED, MANUAL, CONCOLIC
};

enum PathTraceReport {
    ALL_TRACES, CLICK_TRACES, NO_TRACES, HTML_TRACES
};

enum ConcolicTreeOutput {
    TREE_NONE, TREE_FINAL, TREE_ALL
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
        majorMode(AUTOMATED),
        reportPathTrace(NO_TRACES),
        reportPathTraceBytecode(false),
        concolicTreeOutput(TREE_FINAL)
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

    PathTraceReport reportPathTrace;
    bool reportPathTraceBytecode;

    ConcolicTreeOutput concolicTreeOutput;

} Options;

}
#endif // ARTEMISOPTIONS_H
