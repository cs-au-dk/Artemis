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
#include "abstractinputgenerator.h"
#include "termination/terminationstrategy.h"
#include <iostream>

using namespace std;

namespace artemis {

    AbstractInputGenerator::AbstractInputGenerator(QObject *parent, ArtemisOptions* options, ArtemisTopExecutionListener* execution_listener) :
            QObject(parent)
    {
        artemis_options = options;
        m_execution_listener = execution_listener;
    }

    AbstractInputGenerator::~AbstractInputGenerator() {

    }

    ArtemisOptions* AbstractInputGenerator::getOptions() {
        return artemis_options;
    }

    void AbstractInputGenerator::sl_executorExecutedSequence(ExecutableConfiguration conf, ExecutionResult res) {
        m_execution_listener->executed(conf,executor->executor_state(),res);
        executed_sequence(conf,res);
        //We finished one iteration, should we terminate?
        if (termination->should_terminate()) {
            finish_up();
            return;
        } else {
            reprioritize();
            add_new_configurations(conf,res,wl, executor->executor_state());
        }
        if (wl->empty()) {
            finish_up();
            return;
        }

        //Start next iteration
        ExecutableConfiguration new_conf =  wl->remove();
        this->m_execution_listener->before_execute(new_conf,this->executor->executor_state());
        executor->executeSequence(new_conf);
    }

    void AbstractInputGenerator::executed_sequence(const ExecutableConfiguration &conf, const ExecutionResult &res) {
        foreach (QUrl u, res.urls()) {
            urls.add_url(u);
        }
    }

    void AbstractInputGenerator::finish_up() {
        cov = executor->coverage();
        m_execution_listener->artemis_finished(executor->executor_state());
        delete executor;
        delete wl;
        delete termination;
        emit sig_testingDone();
    }

    void AbstractInputGenerator::start() {
        executor =  new WebKitExecutor(this,artemis_options, this->m_execution_listener);
        wl = artemis_options->work_list();
        Q_CHECK_PTR(wl);
        termination = artemis_options->termination();
        Q_CHECK_PTR(termination);
        QObject::connect(executor,SIGNAL(sigExecutedSequence(ExecutableConfiguration,ExecutionResult)),
                         this, SLOT(sl_executorExecutedSequence(ExecutableConfiguration,ExecutionResult)));
        artemis_options->get_listner()->artemis_start(*artemis_options->getURL());
        //Start execution of the empty sequence
        executor->executeSequence(artemis_options->initial_configuration());
    }

    CodeCoverage AbstractInputGenerator::coverage() {
        return cov;
    }

    URLCollector AbstractInputGenerator::urls_collected() {
        return this->urls;
    }

}
