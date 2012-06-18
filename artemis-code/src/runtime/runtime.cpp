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

#include "worklist/deterministicworklist.h"
#include "statistics/statsstorage.h"

#include "runtime.h"

namespace artemis
{

Runtime::Runtime(QObject* parent, ArtemisOptions* options, AbstractInputGenerator* inputgenerator) :
    QObject(parent)
{
    mInputgenerator = inputgenerator;
    mWorklist = options->work_list();
    mOptions = options;
    mTerminationStrategy = options->termination();
    mWebkitExecutor = new WebKitExecutor(this, options, options->get_listner());

    QObject::connect(mWebkitExecutor,
        SIGNAL(sigExecutedSequence(ExecutableConfiguration*, ExecutionResult)), this,
        SLOT(slExecutedSequence(ExecutableConfiguration*, ExecutionResult)));
}

Runtime::~Runtime()
{
    delete mWorklist;
}

void Runtime::start()
{
    mOptions->get_listner()->artemis_start(*mOptions->getURL());

    mWebkitExecutor->executeSequence(mOptions->initial_configuration());
}

void Runtime::slExecutedSequence(ExecutableConfiguration* configuration, ExecutionResult result)
{
    mOptions->get_listner()->executed(configuration, mWebkitExecutor->executor_state(), result);

    foreach (QUrl u, result.urls()) {
        mUrls.add_url(u);
    }

    //We finished one iteration, should we terminate?
    if (mTerminationStrategy->should_terminate()) {
        finish_up();
        return;
    }

    int size_before = mWorklist->size();

    mInputgenerator->reprioritize();
    mInputgenerator->add_new_configurations(configuration, result, mWorklist, mWebkitExecutor->executor_state());

    statistics()->accumulate("InputGenerator::added-configurations", mWorklist->size() - size_before);

    if (mWorklist->empty()) {
        finish_up();
        return;
    }

    //Start next iteration
    ExecutableConfiguration* new_conf = mWorklist->remove();

    mOptions->get_listner()->before_execute(new_conf, mWebkitExecutor->executor_state());
    mWebkitExecutor->executeSequence(new_conf);
}

void Runtime::finish_up() {
    mOptions->get_listner()->artemis_finished(mWebkitExecutor->executor_state());

    mWebkitExecutor->finish_up();

    //delete executor;
    //delete wl;
    //delete termination;

    emit sigTestingDone();
}

URLCollector Runtime::urlsCollected()
{
    return mUrls;
}

CodeCoverage Runtime::coverage() {
    return mWebkitExecutor->coverage();
}

} /* namespace artemis */
