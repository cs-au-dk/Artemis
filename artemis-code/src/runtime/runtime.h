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

#ifndef RUNTIME_H_
#define RUNTIME_H_

#include <QObject>
#include <QUrl>
#include <QNetworkProxy>
#include <set>

#include "strategies/inputgenerator/inputgeneratorstrategy.h"
#include "strategies/inputgenerator/targets/targetgenerator.h"
#include "strategies/termination/terminationstrategy.h"
#include "strategies/prioritizer/prioritizerstrategy.h"

#include "runtime/options.h"
#include "runtime/worklist/worklist.h"
#include "runtime/browser/webkitexecutor.h"
#include "runtime/browser/executionresult.h"
#include "runtime/browser/cookies/immutablecookiejar.h"
#include "runtime/executableconfiguration.h"
#include "runtime/appmodel.h"

namespace artemis
{

class Runtime : public QObject
{
    Q_OBJECT

public:
    Runtime(QObject* parent, const Options& options, QUrl url);

    ~Runtime() {};

    void startAnalysis(QUrl startAnalysis);

private:
    void preConcreteExecution();
    void finishAnalysis();

    AppModelPtr mAppmodel;
    WebKitExecutor* mWebkitExecutor;
    WorkList* mWorklist;
    set<long>* mVisitedStates;

    TerminationStrategy* mTerminationStrategy;
    PrioritizerStrategy* mPrioritizerStrategy;
    InputGeneratorStrategy* mInputgenerator;

    Options mOptions;

private slots:
    void postConcreteExecution(QSharedPointer<ExecutableConfiguration> configuration, QSharedPointer<ExecutionResult> result);

signals:
    void sigTestingDone();

};

} /* namespace artemis */

#endif /* RUNTIME_H_ */
