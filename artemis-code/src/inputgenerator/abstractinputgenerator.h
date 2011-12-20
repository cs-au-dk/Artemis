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
#ifndef ABSTRACTINPUTGENERATOR_H
#define ABSTRACTINPUTGENERATOR_H

#include <QObject>
#include "abstractinputgenerator.h"
#include "artemisoptions.h"
#include "executionresult.h"
#include <worklist/worklist.h>
#include "webkitexecutor.h"
#include "executorstate.h"
#include <QApplication>
#include "coverage/codecoverage.h"
#include "urls/urlcollector.h"
#include "listeners/artemistopexecutionlistener.h"

namespace artemis {

    class ArtemisOptions;

    class AbstractInputGenerator : public QObject
    {
        Q_OBJECT
    public:
        explicit AbstractInputGenerator(QObject *parent = 0, ArtemisOptions* options = 0, ArtemisTopExecutionListener* execution_listener = 0);
        ArtemisOptions* getOptions();
        ~AbstractInputGenerator();


        virtual void start();
        /**
          Method is called when a sequence has been executed. Remember to call super if overwritten!
          */
        virtual void executed_sequence(const ExecutableConfiguration& conf, const ExecutionResult& res);
        virtual void add_new_configurations(const ExecutableConfiguration&, const ExecutionResult&, WorkList*, ExecutorState* exe_state) = 0;
        virtual void reprioritize() = 0;

        CodeCoverage coverage();
        URLCollector urls_collected();


    protected:
        ArtemisOptions* artemis_options;
        WebKitExecutor* executor;
        WorkList* wl;
        TerminationStrategy* termination;
        int iterations;
        void finish_up();

    private:
        CodeCoverage cov;
        URLCollector urls;
        ArtemisTopExecutionListener* m_execution_listener;

    signals:
        void sig_testingDone();

    public slots:
        void sl_executorExecutedSequence(ExecutableConfiguration conf, ExecutionResult res);
    };

}
#endif // ABSTRACTINPUTGENERATOR_H
