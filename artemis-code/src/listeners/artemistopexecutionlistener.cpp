#include "listeners/artemistopexecutionlistener.h"
#include "artemiswebpage.h"
namespace artemis {

ArtemisTopExecutionListener::ArtemisTopExecutionListener()
{
}

//Do nothing dummy functions
void ArtemisTopExecutionListener::artemis_start(const QUrl& url) {}
void ArtemisTopExecutionListener::before_execute(const ExecutableConfiguration& conf, ExecutorState* exe_state) {}
void ArtemisTopExecutionListener::executed(const ExecutableConfiguration& conf, ExecutorState* exe_state, const ExecutionResult& result) {}
void ArtemisTopExecutionListener::loaded_page(const ArtemisWebPage& page, ExecutorState* exe_state) {}
void ArtemisTopExecutionListener::script_crash(QString cause, ExecutorState* exe_state) {}
void ArtemisTopExecutionListener::artemis_finished(ExecutorState* exe_state) {}
void ArtemisTopExecutionListener::eval_called(QString eval_string, ExecutorState* state) {}
void ArtemisTopExecutionListener::code_loaded(QString source, QUrl url, int startline) {}

}
