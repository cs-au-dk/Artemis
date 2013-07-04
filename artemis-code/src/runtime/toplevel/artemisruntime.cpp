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

#include "runtime/worklist/deterministicworklist.h"
#include "util/loggingutil.h"
#include "statistics/statsstorage.h"

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
}

void ArtemisRuntime::run(const QUrl& url)
{
    QSharedPointer<ExecutableConfiguration> initialConfiguration =
        QSharedPointer<ExecutableConfiguration>(new ExecutableConfiguration(QSharedPointer<InputSequence>(new InputSequence()), url));

    mWorklist->add(initialConfiguration, mAppmodel);

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

    ExecutableConfigurationConstPtr nextConfiguration = mWorklist->remove();

    mWebkitExecutor->executeSequence(nextConfiguration); // calls the slExecutedSequence method as callback
}

void ArtemisRuntime::postConcreteExecution(ExecutableConfigurationConstPtr configuration, QSharedPointer<ExecutionResult> result)
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

}
