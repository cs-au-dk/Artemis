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

#include <iostream>

#include "worklist/deterministicworklist.h"
#include "statistics/statsstorage.h"
#include "coverage/coveragetooutputstream.h"
#include "statistics/writers/pretty.h"

#include "runtime.h"

using namespace std;

namespace artemis
{

Runtime::Runtime(QObject* parent,
		WebKitExecutor* webkitExecutor,
		InputGeneratorStrategy* inputgeneratorStrategy,
		PrioritizerStrategy* prioritizer,
		TerminationStrategy* termination,
		MultiplexListener* listener,
		bool dumpUrls) :
    QObject(parent)
{
	mWorklist = new DeterministicWorkList(this);

    mInputgenerator = inputgeneratorStrategy;
    mInputgenerator->setParent(this);

    mTerminationStrategy = termination;
    mTerminationStrategy->setParent(this);

    mPrioritizerStrategy = prioritizer;
    mPrioritizerStrategy->setParent(this);

    mWebkitExecutor = webkitExecutor;
    mWebkitExecutor->setParent(this);

    QObject::connect(mWebkitExecutor,
            SIGNAL(sigExecutedSequence(ExecutableConfiguration*, ExecutionResult)), this,
            SLOT(slExecutedSequence(ExecutableConfiguration*, ExecutionResult)));

    // TODO remove listener dependency
    mListener = listener;
    s_list = new SourceLoadingListener();
    mListener->add_listener(s_list);

    // TODO remove dump URLs
    mDumpUrls = dumpUrls;

}

void Runtime::start(QUrl url)
{
    mListener->artemis_start(url);

    // TODO possible memory leak
    ExecutableConfiguration* initialConfiguration =
    		new ExecutableConfiguration(NULL, new InputSequence(NULL), url);

    mWorklist->add(initialConfiguration, 0);

    runNextIteration();
}

void Runtime::runNextIteration()
{
    qDebug() << "Iteration" << endl;

	if (mWorklist->empty() ||
		mTerminationStrategy->should_terminate()) {

		finish_up();
		return;
	}

	qDebug() << "Iteration END" << endl;

	// TODO remove this memory leak
	ExecutableConfiguration* nextConfiguration = mWorklist->remove();

	mListener->before_execute(nextConfiguration);

	mWebkitExecutor->executeSequence(nextConfiguration);
}

void Runtime::slExecutedSequence(ExecutableConfiguration* configuration, ExecutionResult result)
{
    mListener->executed(configuration, result);

    // TODO remove
    foreach (QUrl u, result.urls()) {
        mUrls.add_url(u);
    }

    mPrioritizerStrategy->reprioritize(mWorklist);

	QList<ExecutableConfiguration*> newConfigurations = mInputgenerator->add_new_configurations(configuration, result);

	foreach (ExecutableConfiguration* newConfiguration, newConfigurations) {
		mWorklist->add(newConfiguration, mPrioritizerStrategy->prioritize(newConfiguration, result));
	}

	statistics()->accumulate("InputGenerator::added-configurations", newConfigurations.size());

	runNextIteration();
}

void Runtime::finish_up() {

    mListener->artemis_finished();

    mWebkitExecutor->finish_up();

	cout << "Artemis: Testing done..." << endl;

	if (mDumpUrls) {
		cout << "The following URLs were encountered:\n";
		urlsCollected().print_urls();
	}

	cout << "\n\n === Coverage information for execution === \n";
	write_coverage_report(cout, coverage());

	cout << "\n==== Source code loaded ====\n";
	s_list->print_results();
	cout << "\n\n";

	cout << "\n=== Statistics ===\n";
	StatsPrettyWriter::write(cout, statistics());
	cout << "\n=== Statistics END ===\n";
	cout << endl;

	qDebug() << "Artemis terminated on: " << QDateTime::currentDateTime().toString() << endl;
	qDebug() << "Build timestamp: " << EXE_BUILD_DATE << endl;

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
