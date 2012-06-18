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

#include "inputgenerator/abstractinputgenerator.h"
#include "worklist/worklist.h"
#include "termination/terminationstrategy.h"
#include "webkitexecutor.h"
#include "executionresult.h"
#include "executableconfiguration.h"

namespace artemis
{

class Runtime : public QObject
{

Q_OBJECT

public:
    Runtime(QObject* parent, ArtemisOptions* options, AbstractInputGenerator* inputgenerator);
    virtual ~Runtime();

    void start();
    URLCollector urlsCollected();
    CodeCoverage coverage();

private:
    void finish_up();

    AbstractInputGenerator* mInputgenerator;
    WorkList* mWorklist;
    ArtemisOptions* mOptions;
    TerminationStrategy* mTerminationStrategy;
    WebKitExecutor* mWebkitExecutor;
    URLCollector mUrls;

private slots:
    void slExecutedSequence(ExecutableConfiguration* configuration, ExecutionResult result);

signals:
    void sigTestingDone();

};

} /* namespace artemis */
#endif /* RUNTIME_H_ */
