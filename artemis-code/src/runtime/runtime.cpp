/*
 Copyright 2011 Simon Holm Jensen. All rights reserved.

 Redistribution and use in source and binary forms, with or without modification, are
 permitted provided that the following conditions are met:

 1. Redistributions of source code must retain the above copyright notice, this list of
 conditions and the following disclaimer.

 2. Redistributions in binary form must reproduce the above copyright notice, this list
 of conditions and the following disclaimer in the documentation and/or other materials
 provided with the distribution.

 THIS SOFTWARE IS PROVIDED BY SIMON HOLM JENSEN ``AS IS'' AND ANY EXPRESS OR IMPLIED
 WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND
 FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL <COPYRIGHT HOLDER> OR
 CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
 ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
 ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

 The views and conclusions contained in the software and documentation are those of the
 authors and should not be interpreted as representing official policies, either expressed
 or implied, of Simon Holm Jensen
 */

#include <assert.h>
#include <iostream>

#include <QSharedPointer>

#include "worklist/deterministicworklist.h"
#include "coverage/coveragetooutputstream.h"
#include "util/coverageutil.h"

#include "statistics/statsstorage.h"
#include "statistics/writers/pretty.h"
#include "strategies/inputgenerator/randominputgenerator.h"
#include "strategies/inputgenerator/event/staticeventparametergenerator.h"
#include "strategies/inputgenerator/form/staticforminputgenerator.h"
#include "strategies/inputgenerator/form/constantstringforminputgenerator.h"
#include "strategies/termination/numberofiterationstermination.h"
#include "strategies/prioritizer/constantprioritizer.h"

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

    mWebkitExecutor = new WebKitExecutor(this, options.presetFormfields, jqueryListener, ajaxRequestListner);

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
    mPrioritizerStrategy = new ConstantPrioritizer(this);

    mWorklist = new DeterministicWorkList(this);

    QObject::connect(mWebkitExecutor, SIGNAL(sigExecutedSequence(QSharedPointer<ExecutableConfiguration>, QSharedPointer<ExecutionResult>)),
                     this, SLOT(postConcreteExecution(QSharedPointer<ExecutableConfiguration>, QSharedPointer<ExecutionResult>)));
}

/**
 * @brief Start the analysis for url
 * @param url
 */
void Runtime::startAnalysis(QUrl url)
{
    qDebug() << "Artemis - Automated tester for JavaScript";
    qDebug() << "Started: " << QDateTime::currentDateTime().toString();
    qDebug() << "Compilation date: " << EXE_BUILD_DATE;
    qDebug() << "-----\n";

    QSharedPointer<ExecutableConfiguration> initialConfiguration =
        QSharedPointer<ExecutableConfiguration>(new ExecutableConfiguration(QSharedPointer<InputSequence>(new InputSequence()), url));

    mWorklist->add(initialConfiguration, 0);

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

    QSharedPointer<ExecutableConfiguration> nextConfiguration = mWorklist->remove();

    mWebkitExecutor->executeSequence(nextConfiguration); // calls the slExecutedSequence method as callback
}

/**
 * @brief Post-concrete-execution
 * @param configuration
 * @param result
 */
void Runtime::postConcreteExecution(QSharedPointer<ExecutableConfiguration> configuration, QSharedPointer<ExecutionResult> result)
{
    mPrioritizerStrategy->reprioritize(mWorklist);

    QList<QSharedPointer<ExecutableConfiguration> > newConfigurations = mInputgenerator->addNewConfigurations(configuration, result);

    foreach(QSharedPointer<ExecutableConfiguration> newConfiguration, newConfigurations) {
        mWorklist->add(newConfiguration, mPrioritizerStrategy->prioritize(newConfiguration, result));
    }

    statistics()->accumulate("InputGenerator::added-configurations", newConfigurations.size());

    preConcreteExecution();
}

void Runtime::finishAnalysis()
{
    qDebug() << "Artemis: Testing done..." << endl;

    qDebug() << "=== Coverage information for execution ===";
    writeCoverageHtml(coverage());
    writeCoverageReport(coverage());

    qDebug() << "\n=== Statistics ===\n";
    StatsPrettyWriter::write(statistics());
    qDebug() << "\n=== Statistics END ===\n";
    qDebug() << endl;

    qDebug() << "Artemis terminated on: " << QDateTime::currentDateTime().toString() << endl;

    emit sigTestingDone();
}

CodeCoverage Runtime::coverage()
{
    return mWebkitExecutor->coverage();
}

} /* namespace artemis */
