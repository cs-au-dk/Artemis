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

#include "model/coverage/coveragetooutputstream.h"
#include "util/loggingutil.h"
#include "model/pathtracer.h"

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

Runtime::Runtime(QObject* parent, const Options& options, const QUrl& url) : QObject(parent)
{
    Log::info("Artemis - Automated tester for JavaScript");
    Log::info("Started: " + QDateTime::currentDateTime().toString().toStdString());
    Log::info("Compilation date: " + ((string) EXE_BUILD_DATE));
    Log::info("-----\n");

    mOptions = options;

    /** Proxy support **/

    if (!options.useProxy.isNull()) {
        QStringList parts = options.useProxy.split(QString(":"));

        QNetworkProxy proxy;
        proxy.setType(QNetworkProxy::HttpProxy);
        proxy.setHostName(parts.at(0));
        if(parts.length() > 1){
            proxy.setPort(parts.at(1).toShort());
        }
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

    mAppmodel = AppModelPtr(new AppModel(options));

    bool enableConstantStringInstrumentation = options.formInputGenerationStrategy == ConstantString;
    mWebkitExecutor = new WebKitExecutor(this, mAppmodel, options.presetFormfields, jqueryListener, ajaxRequestListner, enableConstantStringInstrumentation);

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

    QObject::connect(mWebkitExecutor, SIGNAL(sigAbortedExecution(QString)),
                     this, SLOT(slAbortedExecution(QString)));
    QObject::connect(this, SIGNAL(sigTestingDone()), mWebkitExecutor, SLOT(slTestingDone()));

    /** Visited states **/
    mVisitedStates = new set<long>();
}

void Runtime::done()
{
    QString coveragePath;

    Log::info("Artemis: Testing done...");

    switch (mOptions.outputCoverage) {
    case HTML:
        writeCoverageHtml(mAppmodel->getCoverageListener(), coveragePath);
        break;
    case STDOUT:
         writeCoverageStdout(mAppmodel->getCoverageListener());
         break;
    default:
        break;
    }

    if (mOptions.reportPathTrace == HTML_TRACES) {
        mAppmodel->getPathTracer()->writePathTraceHTML(mOptions.outputCoverage == HTML, coveragePath);
    } else if(mOptions.reportPathTrace != NO_TRACES) {
        Log::info("\n=== Path Tracer ===\n");
        mAppmodel->getPathTracer()->write();
        Log::info("=== Path Tracer END ===\n");
    }

    statistics()->accumulate("WebKit::coverage::covered-unique", mAppmodel->getCoverageListener()->getNumCoveredLines());

    Log::info("\n=== Statistics ===\n");
    StatsPrettyWriter::write(statistics());
    Log::info("\n=== Statistics END ===\n\n");

    Log::info("\n=== Last pathconditions ===\n");
    Log::info(mWebkitExecutor->webkitListener->generatePathConditionString().toStdString());
    Log::info("=== Last pathconditions END ===\n\n");

    Log::info("Artemis terminated on: "+ QDateTime::currentDateTime().toString().toStdString());

    emit sigTestingDone();
}

void Runtime::slAbortedExecution(QString reason)
{
    cerr << reason.toStdString() << std::endl;
    emit sigTestingDone();
}

} /* namespace artemis */
