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

#include "concolicreorderingruntime.h"

#include "util/loggingutil.h"

namespace artemis
{

ConcolicReorderingRuntime::ConcolicReorderingRuntime(QObject* parent, const Options& options, const QUrl& url)
    : Runtime(parent, options, url)
    , mNumIterations(0)
{
    // This web view is not used and not shown, but is required to give proper geometry to the ArtemisWebPage which
    // renders the site being tested. It is required to have proper geometry in order to click correctly on elements.
    // Without this the "bare" ArtemisWebPage is laid out correctly but the document element has zero size, so any
    // click is outside its boundary and is not recognised.
    mWebView = ArtemisWebViewPtr(new ArtemisWebView());
    mWebView->setPage(mWebkitExecutor->getPage().data());
    //mWebView->resize(1000,1000);
    //mWebView->show();

    // Running iterations
    QObject::connect(mWebkitExecutor, SIGNAL(sigExecutedSequence(ExecutableConfigurationConstPtr, QSharedPointer<ExecutionResult>)),
                     this, SLOT(postConcreteExecution(ExecutableConfigurationConstPtr, QSharedPointer<ExecutionResult>)));

    // Managing timers
    QObject::connect(mWebkitExecutor->mWebkitListener, SIGNAL(addedTimer(int, int, bool)),
                     this, SLOT(slTimerAdded(int, int, bool)));
    QObject::connect(mWebkitExecutor->mWebkitListener, SIGNAL(removedTimer(int)),
                     this, SLOT(slTimerRemoved(int)));
    // Do not capture AJAX callbacks, force them to be fired synchronously.
    QWebExecutionListener::getListener()->doNotCaptureAjaxCallbacks();
}

void ConcolicReorderingRuntime::run(const QUrl &url)
{
    mUrl = url;

    setupInitialActionSequence();

    // There is nothing else to prepare... Start the first iteration.
    Log::info(QString("Beginning analysis of %1").arg(url.toString()).toStdString());
    preConcreteExecution();
}


void ConcolicReorderingRuntime::preConcreteExecution()
{
    // Begins a new iteration and initiates the new page load.

    // Check if we have reached the iteration limit.
    if (mOptions.iterationLimit > 0 && mOptions.iterationLimit <= mNumIterations) {
        Log::info("Iteration limit reached");
        mWebkitExecutor->detach();
        done();
        return;
    }
    mNumIterations++;

    Log::debug("\n============= New-Iteration =============");
    Log::info(QString("Iteration %1:").arg(mNumIterations).toStdString());
    clearStateForNewIteration();

    // N.B. Unlike the main concolic mode (concolicruntime.cpp), we do not do the input actions as part of the configuration.
    // This mode works more like server mode: we let WebkitExecutor do the page load and nothing more.
    // Then this runtime takes over and manages the concolic trace recording and form injections directly.
    ExecutableConfigurationPtr noInput = ExecutableConfigurationPtr(new ExecutableConfiguration(InputSequencePtr(new InputSequence()), mUrl));
    mWebkitExecutor->executeSequence(noInput, MODE_CONCOLIC_NO_TRACE); // Calls postConcreteExecution as a callback
}

void ConcolicReorderingRuntime::clearStateForNewIteration()
{
    // Clear all cookies.
    // In this mode the cookie jar will always be of type ResettableCookieJar (see options.saveCookiesForSession in artemis.cpp).
    QNetworkCookieJar* cookieJar = mWebkitExecutor->getCookieJar();
    ResettableCookieJar* resettableCookieJar = dynamic_cast<ResettableCookieJar*>(cookieJar);
    if (resettableCookieJar) {
        resettableCookieJar->reset();
    }
}


void ConcolicReorderingRuntime::postConcreteExecution(ExecutableConfigurationConstPtr configuration, QSharedPointer<ExecutionResult> result)
{
    // Called once we have finished the page load. Now it is time to begin the trace execution.

    // Process any async events which already exist immediately after the page load.
    clearAsyncEvents();

    // Execute the current action sequence
    executeCurrentActionSequence();

    // Choose the new values and actions to test
    chooseNextSequenceAndExplore();

}



void ConcolicReorderingRuntime::slTimerAdded(int timerId, int timeout, bool singleShot)
{
    assert(!mTimers.contains(timerId));
    mTimers.insert(timerId, QPair<int, bool>(timeout, singleShot));
}

void ConcolicReorderingRuntime::slTimerRemoved(int timerId)
{
    // N.B. clearAsyncEvents removes IDs manually, so we do no necessarily expect timerId to still be in mTimers.
    mTimers.remove(timerId);
}

// TODO: This is duplicated from analysisserverruntime.cpp
void ConcolicReorderingRuntime::clearAsyncEvents()
{
    // AJAX events are handled synchronously (see call to doNotCaptureAjaxCallbacks in the constructor) so they are ignored here.

    // Fire all timers up to depth 4. i.e. 4 levels of nested timers, or 4 rounds of interval timers.
    for (int i = 0; i < 4 && !mTimers.isEmpty(); i++) {
        QList<int> currentRoundTimers = mTimers.keys();
        qSort(currentRoundTimers); // Take timers in ID order.
        Log::debug(QString("  CAE: Firing timers in round %1 (%2 timers)").arg(i).arg(currentRoundTimers.length()).toStdString());
        foreach(int timerId, currentRoundTimers) {
            if (!mTimers.contains(timerId)) {
                continue; // This timer must have been removed by an earlier timer in this round.
            }
            bool singleShot = mTimers[timerId].second;

            Log::debug(QString("  CAE: Fire timer %1").arg(timerId).toStdString());
            // N.B. This may add new timers to mTimers, which we will pick up in the next round.
            mWebkitExecutor->mWebkitListener->timerFire(timerId);
            Statistics::statistics()->accumulate("ConcolicReordering::ClearAsyncEvents::TimersTriggered", 1);
            if (singleShot) {
                mTimers.remove(timerId); // This will also get removed by timerCancel, but it may not be immediate.
                mWebkitExecutor->mWebkitListener->timerCancel(timerId);
                Statistics::statistics()->accumulate("ConcolicReordering::ClearAsyncEvents::TimersTriggered", 1);
            }
        }
    }

    // Cancel any outstanding timers.
    foreach (int timerId, mTimers.keys()) {
        Log::debug(QString("  CAE: Cancelling timer %1").arg(timerId).toStdString());
        mTimers.remove(timerId); // This will also get removed by timerCancel, but it may not be immediate.
        mWebkitExecutor->mWebkitListener->timerCancel(timerId);
        Statistics::statistics()->accumulate("ConcolicReordering::ClearAsyncEvents::TimersCancelled", 1);
    }

    // Now all async events are executed or removed, so there should be no background execution in the browser.
}



void ConcolicReorderingRuntime::setupInitialActionSequence()
{
    // TODO
}

void ConcolicReorderingRuntime::executeCurrentActionSequence()
{
    // TODO
}

void ConcolicReorderingRuntime::chooseNextSequenceAndExplore()
{
    // TODO
    done();
}





} // namespace artemis
