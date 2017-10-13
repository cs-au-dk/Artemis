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

#include "runtime/worklist/deterministicworklist.h"
#include "util/loggingutil.h"
#include "statistics/statsstorage.h"
#include "runtime/input/baseinput.h"
#include "runtime/input/dominput.h"
#include "strategies/inputgenerator/targets/concolictarget.h"
#include "symbolic/symbolicinterpreter.h"

#include "artemisruntime.h"

namespace artemis
{

ArtemisRuntime::ArtemisRuntime(QObject* parent, const Options& options, const QUrl& url) :
    Runtime(parent, options, url)
{
    mIterations = 1;
    QObject::connect(mWebkitExecutor, SIGNAL(sigExecutedSequence(ExecutableConfigurationConstPtr, QSharedPointer<ExecutionResult>)),
                     this, SLOT(postConcreteExecution(ExecutableConfigurationConstPtr, QSharedPointer<ExecutionResult>)));

    mWorklist = WorkListPtr(new DeterministicWorkList(mPrioritizerStrategy));

    // Force the browser window to have a size.
    mWebView = ArtemisWebViewPtr(new ArtemisWebView());
    mWebView->setPage(mWebkitExecutor->getPage().data());
    mWebView->forceResize(1200,800); // TODO: Pull size from mOptions.

    // Enable symbolic target support for ConcolicTargetGenerator to use.
    Symbolic::SymbolicInterpreter::setFeatureSymbolicEventTargetEnabled(true);
    
    // If the load-new-urls option is set, we need to log scheduled page loads.
    if (mOptions.artemisLoadUrls) {
        QObject::connect(mWebkitExecutor->getPage().data(), SIGNAL(sigNavigationRequest(QWebFrame*,QNetworkRequest,QWebPage::NavigationType)),
                         this, SLOT(slNavigationRequest(QWebFrame*,QNetworkRequest,QWebPage::NavigationType)));
    }
}

void ArtemisRuntime::run(const QUrl& url)
{
    QSharedPointer<ExecutableConfiguration> initialConfiguration =
        QSharedPointer<ExecutableConfiguration>(new ExecutableConfiguration(QSharedPointer<InputSequence>(new InputSequence()), url));
    mUrlsSeen.clear();
    mUrlsSeen.insert(url);

    mWorklist->add(initialConfiguration, mAppmodel);

    if (mOptions.enableEventVisibilityFiltering) {
        Statistics::statistics()->set("WebKit::events::skipped::visibility", 0);
    }

    preConcreteExecution();
}

void ArtemisRuntime::preConcreteExecution()
{
    if (mWorklist->empty() ||
        mTerminationStrategy->shouldTerminate()) {
        if(!((mIterations-1)%25)){
            cout << "\n";
        }
        cout << "\n" << endl;

        mWebkitExecutor->detach();
        mExecStat->generateOutput();
        done();
        return;
    }

    int mod = mIterations%25;

    if(!(mod) && mIterations){
        cout << "\r ..... ..... ..... ..... .....    " << mIterations << " ";
    } else {
        if(mod == 1){
            cout << endl;
        }
        cout << "\r";
        for(int i=0; i < mod; i++){
            if(!(i%5)){
                cout << " ";
            }
            cout << ".";
        }
        for(int i= mod; i < 25; i++){
            if(!(i%5)){
                cout << " ";
            }
            cout << " ";
        }
        cout << "    "<< mIterations << " ";
    }
    cout.flush();

    mIterations++;
    Log::debug("\n============= New-Iteration =============");
    Log::debug("--------------- WORKLIST ----------------\n");
    Log::debug(mWorklist->toString().toStdString());
    Log::debug("--------------- COVERAGE ----------------\n");
    Log::debug(mAppmodel->getCoverageListener()->toString().toStdString());

    mExecStat->beginNewIteration();

    ExecutableConfigurationConstPtr nextConfiguration = mWorklist->remove();

    mWebkitExecutor->executeSequence(nextConfiguration, mOptions.targetStrategy == TARGET_CONCOLIC ? MODE_CONCOLIC_LAST_EVENT : MODE_CONCOLIC); // calls the postConcreteExecution method as callback
}

void ArtemisRuntime::postConcreteExecution(ExecutableConfigurationConstPtr configuration, ExecutionResultPtr result)
{
    notifyAboutNewIteration(configuration);

    mLatestFormFields = result->getFormFields();

    mWorklist->reprioritize(mAppmodel);

    if (!mOptions.disableStateCheck) {

        long hash = result->getPageStateHash();
        if (mVisitedStates.find(hash) != mVisitedStates.end()) {

            qDebug() << "Page state has already been seen";
            preConcreteExecution();
            return;
        }

        qDebug() << "Visiting new state";
        mVisitedStates.insert(hash);
    }

    // Generate new inputs
    QList<QSharedPointer<ExecutableConfiguration> > newConfigurations = mInputgenerator->addNewConfigurations(configuration, result);
    foreach(QSharedPointer<ExecutableConfiguration> newConfiguration, newConfigurations) {
        mWorklist->add(newConfiguration, mAppmodel);
    }

    Statistics::statistics()->accumulate("InputGenerator::added-configurations", newConfigurations.size());
    preConcreteExecution();
}


void ArtemisRuntime::notifyAboutNewIteration(ExecutableConfigurationConstPtr configuration)
{
    // If the previously executed trace used a ConcolicTarget, then we must notify the corresponding analysis about the new trace.
    // Otherwise ignore.

    if (configuration->getInputSequence()->length() < 1) {
        return;
    }

    DomInputConstPtr input = configuration->getInputSequence()->getLast().dynamicCast<const DomInput>();
    if (input.isNull()) {
        return;
    }

    ConcolicTargetDescriptorConstPtr target = input->getTarget().dynamicCast<const ConcolicTarget>();
    if (target.isNull()) {
        return;
    }

    // Add the trace into the analysis, passing in the ExplorationHandle which lets the analysis know where this run was expected to exlpore.
    target->getAnalysis()->addTrace(mWebkitExecutor->getTraceBuilder()->trace(), target->getExplorationTarget());
}



void ArtemisRuntime::slNavigationRequest(QWebFrame* frame, QNetworkRequest request, QWebPage::NavigationType type)
{
    if (mOptions.artemisLoadUrls) {
        // Page loads are not executed during the iteration, but when we notice them, they are added to the worklist as a new entry-point to try.
        if (!mUrlsSeen.contains(request.url())) {
            Log::debug(QString("Adding URL to worklist: %1").arg(request.url().toString()).toStdString());
            QSharedPointer<ExecutableConfiguration> newUrlConfiguration = QSharedPointer<ExecutableConfiguration>(new ExecutableConfiguration(QSharedPointer<InputSequence>(new InputSequence()), request.url()));
            mUrlsSeen.insert(request.url());
            mWorklist->add(newUrlConfiguration, mAppmodel);
        }
    }
}


} // namespace artemis
