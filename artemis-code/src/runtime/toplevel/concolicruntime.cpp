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

#include "util/loggingutil.h"
#include "concolic/executiontree/tracemerger.h"

#include "concolicruntime.h"

namespace artemis
{


ConcolicRuntime::ConcolicRuntime(QObject* parent, const Options& options, const QUrl& url) :
    Runtime(parent, options, url)
{
    QObject::connect(mWebkitExecutor, SIGNAL(sigExecutedSequence(ExecutableConfigurationConstPtr, QSharedPointer<ExecutionResult>)),
                     this, SLOT(postConcreteExecution(ExecutableConfigurationConstPtr, QSharedPointer<ExecutionResult>)));


}

void ConcolicRuntime::run(const QUrl& url)
{
    QSharedPointer<ExecutableConfiguration> initialConfiguration =
        QSharedPointer<ExecutableConfiguration>(new ExecutableConfiguration(QSharedPointer<InputSequence>(new InputSequence()), url));

    mNextConfiguration = initialConfiguration;

    preConcreteExecution();
}

void ConcolicRuntime::preConcreteExecution()
{
    if (mNextConfiguration.isNull()) {
        mWebkitExecutor->detach();
        done();
        return;
    }

    Log::debug("\n============= New-Iteration =============");
    Log::debug("--------------- COVERAGE ----------------\n");
    Log::debug(mAppmodel->getCoverageListener()->toString().toStdString());

    mWebkitExecutor->executeSequence(mNextConfiguration); // calls the postConcreteExecution method as callback
}

void ConcolicRuntime::postConcreteExecution(ExecutableConfigurationConstPtr configuration, QSharedPointer<ExecutionResult> result)
{
    // Merge trace with tracegraph
    TraceMerger::merge(mSymbolicExecutionGraph, mWebkitExecutor->getTraceBuilder()->trace());

    // Generate new input
    // TODO
    mNextConfiguration.clear();

    // Execute next iteration
    preConcreteExecution();
}



} // namespace artemis

