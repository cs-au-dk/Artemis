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

#include <assert.h>
#include <iostream>

#include <QSharedPointer>

#include "worklist/deterministicworklist.h"
#include "model/coverage/coveragetooutputstream.h"
#include "util/loggingutil.h"

#include "statistics/statsstorage.h"
#include "statistics/writers/pretty.h"
#include "strategies/inputgenerator/randominputgenerator.h"
#include "strategies/inputgenerator/event/staticeventparametergenerator.h"
#include "strategies/inputgenerator/form/staticforminputgenerator.h"
#include "strategies/inputgenerator/form/constantstringforminputgenerator.h"
#include "strategies/termination/numberofiterationstermination.h"

#include "strategies/prioritizer/constantprioritizer.h"
#include "strategies/prioritizer/randomprioritizer.h"
#include "strategies/prioritizer/coverageprioritizer.h"
#include "strategies/prioritizer/readwriteprioritizer.h"
#include "strategies/prioritizer/collectedprioritizer.h"

#include "runtime.h"

using namespace std;

namespace artemis
{

/**
 * This is the main-loop used by artemis.
 *
 * startAnalysis -> preConcreteExecution -> postConcreteExecution -> finishAnalysis
 *                              ^------------------|
 */
Runtime::Runtime(QObject* parent, const Options& options, QUrl url) : QObject(parent)
{

    mOptions = options;

    /** Proxy support **/

    if (!options.useProxy.isNull()) {
        QStringList parts = options.useProxy.split(QString(":"));
        QNetworkProxy proxy(QNetworkProxy::HttpProxy, parts.at(0), parts.at(1).toShort());
        QNetworkProxy::setApplicationProxy(proxy);
    }

    /** Ajax support and cookie injection **/

    AjaxRequestListener* ajaxRequestListner = new AjaxRequestListener(NULL);

    ImmutableCookieJar* immutableCookieJar = new ImmutableCookieJar(
        options.presetCookies, url.host());
    ajaxRequestListner->setCookieJar(immutableCookieJar);

    /** JQuery support **/

    JQueryListener* jqueryListener = new JQueryListener(this);

    /** Runtime Objects **/

    mAppmodel = AppModelPtr(new AppModel());

    mWebkitExecutor = new WebKitExecutor(this, mAppmodel, options.presetFormfields, jqueryListener, ajaxRequestListner);

    QSharedPointer<FormInputGenerator> formInputGenerator;
    switch (options.formInputGenerationStrategy) {
    case Random:
        formInputGenerator = QSharedPointer<StaticFormInputGenerator>(new StaticFormInputGenerator());
        break;

    case ConstantString:
        formInputGenerator = QSharedPointer<ConstantStringFormInputGenerator>(new ConstantStringFormInputGenerator());
        break;

    default:
        assert(false);
    }

    mInputgenerator = new RandomInputGenerator(this,
                                               formInputGenerator,
                                               QSharedPointer<StaticEventParameterGenerator>(new StaticEventParameterGenerator()),
                                               new TargetGenerator(this, jqueryListener),
                                               options.numberSameLength);
    mTerminationStrategy = new NumberOfIterationsTermination(this, options.iterationLimit);

    switch (options.prioritizerStrategy) {
    case CONSTANT:
        mPrioritizerStrategy = PrioritizerStrategyPtr(new ConstantPrioritizer());
        break;
    case RANDOM:
        mPrioritizerStrategy = PrioritizerStrategyPtr(new RandomPrioritizer());
        break;
    case COVERAGE:
        mPrioritizerStrategy = PrioritizerStrategyPtr(new CoveragePrioritizer());
        break;
    case READWRITE:
        mPrioritizerStrategy = PrioritizerStrategyPtr(new ReadWritePrioritizer());
        break;
    case  ALL_STRATEGIES:{
        CollectedPrioritizer* strategy = new CollectedPrioritizer();
        strategy->addPrioritizer(new ConstantPrioritizer());
        strategy->addPrioritizer(new CoveragePrioritizer());
        strategy->addPrioritizer(new ReadWritePrioritizer());
        mPrioritizerStrategy = PrioritizerStrategyPtr(strategy);}
        break;
    default:
        assert(false);
    }

    mWorklist = WorkListPtr(new DeterministicWorkList(mPrioritizerStrategy));

    QObject::connect(mWebkitExecutor, SIGNAL(sigExecutedSequence(ExecutableConfigurationConstPtr, QSharedPointer<ExecutionResult>)),
                     this, SLOT(postConcreteExecution(ExecutableConfigurationConstPtr, QSharedPointer<ExecutionResult>)));
    QObject::connect(mWebkitExecutor, SIGNAL(sigAbortedExecution(QString)),
                     this, SLOT(slAbortedExecution(QString)));


    /** Visited states **/
    mVisitedStates = new set<long>();
}

/**
 * @brief Start the analysis for url
 * @param url
 */
void Runtime::startAnalysis(QUrl url)
{
    Log::info("Artemis - Automated tester for JavaScript");
    Log::info("Started: " + QDateTime::currentDateTime().toString().toStdString());
    Log::info("Compilation date: " + ((string) EXE_BUILD_DATE));
    Log::info( "-----\n");

    QSharedPointer<ExecutableConfiguration> initialConfiguration =
        QSharedPointer<ExecutableConfiguration>(new ExecutableConfiguration(QSharedPointer<InputSequence>(new InputSequence()), url));

    mWorklist->add(initialConfiguration, mAppmodel);

    preConcreteExecution();
}

/**
 * @brief Pre-concrete-execution
 */
void Runtime::preConcreteExecution()
{
    if (mWorklist->empty() ||
        mTerminationStrategy->shouldTerminate()) {

        mWebkitExecutor->detach();
        finishAnalysis();
        return;
    }

    Log::debug("\n============= New-Iteration =============");
    Log::debug("--------------- WORKLIST ----------------\n");
    Log::debug(mWorklist->toString().toStdString());
    Log::debug("--------------- COVERAGE ----------------\n");
    Log::debug(mAppmodel->getCoverageListener()->toString().toStdString());

    ExecutableConfigurationConstPtr nextConfiguration = mWorklist->remove();

    mWebkitExecutor->executeSequence(nextConfiguration); // calls the slExecutedSequence method as callback
}

/**
 * @brief Post-concrete-execution
 * @param configuration
 * @param result
 */
void Runtime::postConcreteExecution(ExecutableConfigurationConstPtr configuration, QSharedPointer<ExecutionResult> result)
{
    mWorklist->reprioritize(mAppmodel);

    long hash;
    if (mOptions.disableStateCheck ||
            mVisitedStates->find(hash = result->getPageStateHash()) == mVisitedStates->end()) {

        qDebug() << "Visiting new state";

        mVisitedStates->insert(hash);
        QList<QSharedPointer<ExecutableConfiguration> > newConfigurations = mInputgenerator->addNewConfigurations(configuration, result);

        foreach(QSharedPointer<ExecutableConfiguration> newConfiguration, newConfigurations) {
            mWorklist->add(newConfiguration, mAppmodel);
        }

        statistics()->accumulate("InputGenerator::added-configurations", newConfigurations.size());

    } else {
        qDebug() << "Page state has already been seen";
    }

    preConcreteExecution();
}

void Runtime::finishAnalysis()
{
    Log::info("Artemis: Testing done...");

    switch (mOptions.outputCoverage) {
    case HTML:
        writeCoverageHtml(mAppmodel->getCoverageListener());
        break;
    case STDOUT:
         writeCoverageStdout(mAppmodel->getCoverageListener());
         break;
    default:
        break;
    }

    statistics()->accumulate("WebKit::coverage::covered-unique", mAppmodel->getCoverageListener()->getNumCoveredLines());

    Log::info("\n=== Statistics ===\n");
    StatsPrettyWriter::write(statistics());
    Log::info("\n=== Statistics END ===\n\n");
    Log::info("Artemis terminated on: "+ QDateTime::currentDateTime().toString().toStdString());

    emit sigTestingDone();
}

void Runtime::slAbortedExecution(QString reason)
{
    cerr << reason.toStdString() << std::endl;
    emit sigTestingDone();
}

} /* namespace artemis */
