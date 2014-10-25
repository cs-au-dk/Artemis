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

#include <assert.h>
#include <iostream>

#include <QSharedPointer>
#include <QDebug>

#include "model/coverage/coveragetooutputstream.h"
#include "util/loggingutil.h"
#include "util/fileutil.h"
#include "model/pathtracer.h"

#include "model/seleniumeventexecutionstatistics.h"
#include "model/jsoneventexecutionstatistics.h"
#include "model/stubeventexecutionstatistics.h"


#include "statistics/statsstorage.h"

#include "strategies/inputgenerator/randominputgenerator.h"
#include "strategies/inputgenerator/event/staticeventparametergenerator.h"
#include "strategies/inputgenerator/form/staticforminputgenerator.h"
#include "strategies/inputgenerator/form/constantstringforminputgenerator.h"

#include "strategies/inputgenerator/targets/jquerytargetgenerator.h"
#include "strategies/inputgenerator/targets/legacytargetgenerator.h"
#include "strategies/inputgenerator/targets/concolictargetgenerator.h"

#include "strategies/termination/numberofiterationstermination.h"

#include "strategies/prioritizer/constantprioritizer.h"
#include "strategies/prioritizer/randomprioritizer.h"
#include "strategies/prioritizer/coverageprioritizer.h"
#include "strategies/prioritizer/readwriteprioritizer.h"
#include "strategies/prioritizer/collectedprioritizer.h"

#include "concolic/solver/z3solver.h"
#include "concolic/solver/kaluzasolver.h"
#include "concolic/solver/cvc4solver.h"
#include "concolic/pathcondition.h"

#include "runtime.h"

using namespace std;

namespace artemis
{

Runtime::Runtime(QObject* parent, const Options& options, const QUrl& url)
    : QObject(parent)
    , mDisabledFeatures(options.concolicDisabledFeatures)
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
    bool enablePropertyAccessInstrumentation = options.prioritizerStrategy == READWRITE;
    mWebkitExecutor = new WebKitExecutor(this, mAppmodel, options.presetFormfields,
                                         jqueryListener, ajaxRequestListner,
                                         enableConstantStringInstrumentation,
                                         enablePropertyAccessInstrumentation,
                                         options.concolicDisabledFeatures);

    if(!options.customUserAgent.isEmpty()) {
        mWebkitExecutor->getPage()->setCustomUserAgent(options.customUserAgent);
    }

    if(options.reportHeap != NO_CALLS){
        mWebkitExecutor->mWebkitListener->enableHeapReport(options.reportHeap == NAMED_CALLS, 0, options.heapReportFactor);
    }

    QSharedPointer<FormInputGenerator> formInputGenerator;
    switch (options.formInputGenerationStrategy) {
    case Random:
        formInputGenerator = StaticFormInputGeneratorPtr(new StaticFormInputGenerator(options.presetFormfields.keys()));
        break;

    case ConstantString:
        formInputGenerator = ConstantStringFormInputGeneratorPtr(new ConstantStringFormInputGenerator(options.presetFormfields.keys()));
        break;

    default:
        assert(false);
    }

    switch(options.exportEventSequence){
    case DONT_EXPORT:
        mExecStat = new StubEventExecutionStatistics;
        break;
    case EXPORT_SELENIUM:
        mExecStat = new SeleniumEventExecutionStatistics(url);
        break;
    case EXPORT_JSON:
        mExecStat = new JSONEventExecutionStatistics(url);  
        break;

    default:
        assert(false);
    }

    switch(options.targetStrategy) {
    case TARGET_CONCOLIC:
        mTargetGenerator = TargetGeneratorConstPtr(new ConcolicTargetGenerator(mWebkitExecutor->getTraceBuilder()));
        break;
    case TARGET_JQUERY:
        mTargetGenerator = TargetGeneratorConstPtr(new JqueryTargetGenerator(jqueryListener));
        break;
    case TARGET_LEGACY:
        mTargetGenerator = TargetGeneratorConstPtr(new LegacyTargetGenerator());
        break;

    default:
        assert(false);
    }

    mInputgenerator = new RandomInputGenerator(this,
                                               formInputGenerator,
                                               QSharedPointer<StaticEventParameterGenerator>(new StaticEventParameterGenerator()),
                                               mTargetGenerator,
                                               mExecStat,
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
    case ALL_STRATEGIES:{
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
}

void writeAndWrapReportBuffer(int nm, QString buffer){
    QString numberStr = QString::number(nm);
    buffer = QString("{\"heap-report\":[").append(buffer).append(QString("]}"));
    writeStringToFile(QString("heap-report-") + QDateTime::currentDateTime().toString("dd-MM-yy-hh-mm-ss")+" ("+numberStr+").json",buffer);

}

void Runtime::done()
{
    QString coveragePath;
    QString tracerPath;

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

    // Do some last-minute statistics

    Statistics::statistics()->accumulate("WebKit::coverage::covered-unique", (int)mAppmodel->getCoverageListener()->getNumCoveredLines());

    // solve the last PC - this is needed by some system tests
    PathConditionPtr pc = PathCondition::createFromTrace(mWebkitExecutor->getTraceBuilder()->trace());

    if (!pc.isNull() && mOptions.concolicNegateLastConstraint) {
        pc->negateLastCondition();
    }

    SolverPtr solver = Solver::getSolver(mOptions);
    SolutionPtr solution = solver->solve(
                pc,
                FormFieldRestrictedValues::getRestrictions(mLatestFormFields, mWebkitExecutor->getPage()));

    solution->toStatistics();

    // Print final output

    if (mOptions.reportPathTrace == HTML_TRACES) {
        mAppmodel->getPathTracer()->writePathTraceHTML(mOptions.outputCoverage == HTML, coveragePath, tracerPath);
    } else if(mOptions.reportPathTrace != NO_TRACES) {
        Log::info("\n=== Path Tracer ===\n");
        mAppmodel->getPathTracer()->write();
        Log::info("=== Path Tracer END ===\n");
    }

    mAppmodel->getPathTracer()->writeStatistics();

    if(mOptions.reportHeap != NO_CALLS){
        QString buffer = "";
        int i = 0;
        int nm;
        QList<QString> report = mWebkitExecutor->mWebkitListener->getHeapReport(nm);
        foreach(QString rap, report){
            buffer += rap;
            if (i < report.length()-1){
                buffer += QString(", ");
            }
            i++;
        }
        if(buffer.length() > 0){
            writeAndWrapReportBuffer(nm,buffer);
        }

    }

    Log::info("\n=== Statistics ===\n");
    Statistics::statistics()->writeToStdOut();
    Log::info("\n=== Statistics END ===\n\n");

    Log::info("\n=== Last pathconditions ===\n");
    //Log::info(pc->toStatisticsValuesString(true));
    Log::info(pc->toStatisticsString());
    Log::info("=== Last pathconditions END ===\n\n");

    Log::info("Artemis terminated on: "+ QDateTime::currentDateTime().toString().toStdString());

    exit(0);

    // TODO, see next TODO
    emit sigTestingDone();
}

void Runtime::slAbortedExecution(QString reason)
{
    cerr << reason.toStdString() << std::endl;
    exit(1);

    // TODO we should use this emit, but we have some race conditions happening when Artemis shuts down.
    emit sigTestingDone();
}

} /* namespace artemis */
