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

#ifndef CONCOLICSTANDALONERUNTIME_H
#define CONCOLICSTANDALONERUNTIME_H

#include <QObject>
#include <QUrl>

#include "runtime/runtime.h"
#include "runtime/options.h"
#include "concolic/concolicanalysis.h"

namespace artemis
{

// TODO: Add something like ConcolicRuntime::reportStatistics() to call during done().
// TODO: Add support for async events: timers and AJAX, as we do in server mode.

class ConcolicStandaloneRuntime : public Runtime
{
    Q_OBJECT

public:
    ConcolicStandaloneRuntime(QObject* parent, const Options& options, const QUrl& url);

    void run(const QUrl& url);

protected:
    QUrl mUrl;

    QString loadJsSnippet();
    QString mJsFilename;
    QString mJsCode;

    // Concolic analysis part
    ConcolicAnalysisPtr mConcolicAnalysis;
    ConcolicAnalysis::ExplorationResult mExplorationResult;

    int mNumIterations;

    void newConcolicIteration();
    void doneConcolicIteration(TraceNodePtr trace);

    // Logging part
    // TODO: The common parts of tree output from here, Concolic Runtime, and AnalysisServerRuntime (from feature-server-mode) should be merged. Maybe ConcolicAnalysis could handle this?
    void concolicOutputTree();

    void done();
    void reportStatistics();

protected slots:
    void slExecutedSequence(ExecutableConfigurationConstPtr configuration, QSharedPointer<ExecutionResult> result);

};


} // namespace artemis
#endif // CONCOLICSTANDALONERUNTIME_H
