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

#ifndef CONCOLICREORDERINGRUNTIME_H
#define CONCOLICREORDERINGRUNTIME_H

#include <QUrl>

#include "runtime/runtime.h"
#include "runtime/options.h"
#include "runtime/browser/artemiswebview.h"

#include "concolic/concolicanalysis.h"


namespace artemis
{

class ConcolicReorderingRuntime : public Runtime
{
    Q_OBJECT

public:
    ConcolicReorderingRuntime(QObject* parent, const Options& options, const QUrl& url);

    void run(const QUrl& url);

protected:
    QUrl mUrl;
    ArtemisWebViewPtr mWebView;
    int mNumIterations;

    // Browser part
    void preConcreteExecution();
    void clearStateForNewIteration();
    QMap<int, QPair<int, bool> > mTimers;
    void clearAsyncEvents();

    // Action ordering and execution
    void setupInitialActionSequence();
    void executeCurrentActionSequence();
    void chooseNextSequenceAndExplore();

protected slots:
    // Browser part
    void postConcreteExecution(ExecutableConfigurationConstPtr configuration, QSharedPointer<ExecutionResult> result);
    void slTimerAdded(int timerId, int timeout, bool singleShot);
    void slTimerRemoved(int timerId);


};

} // namespace artemis
#endif // CONCOLICREORDERINGRUNTIME_H
