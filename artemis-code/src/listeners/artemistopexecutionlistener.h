#ifndef ARTEMISTOPEXECUTIONLISTENER_H
#define ARTEMISTOPEXECUTIONLISTENER_H

#include <QtWebKit>
#include <executableconfiguration.h>
#include "executorstate.h"
#include "executionresult.h"
#include "artemiswebpage.h"

namespace artemis {

    class ArtemisTopExecutionListener
    {
    public:
        ArtemisTopExecutionListener();
        virtual void artemis_start(const QUrl& url);
        virtual void before_execute(const ExecutableConfiguration& conf, ExecutorState* exe_state);
        virtual void executed(const ExecutableConfiguration& conf, ExecutorState* exe_state, const ExecutionResult& result);
        virtual void loaded_page(const ArtemisWebPage& page, ExecutorState* exe_state);
        virtual void script_crash(QString cause, ExecutorState* exe_state);
        virtual void artemis_finished(ExecutorState* exe_state);
        virtual void eval_called(QString eval_string, ExecutorState* state);
        virtual void code_loaded(QString source, QUrl url, int startline);
    };

}
#endif // ARTEMISTOPEXECUTIONLISTENER_H
