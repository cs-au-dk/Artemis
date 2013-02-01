#include "listeners/artemistopexecutionlistener.h"
#include "runtime/browser/artemiswebpage.h"
namespace artemis {

ArtemisTopExecutionListener::ArtemisTopExecutionListener()
{
}

//Do nothing dummy functions
void ArtemisTopExecutionListener::artemis_start(const QUrl& url) {}
void ArtemisTopExecutionListener::before_execute(ExecutableConfiguration* conf) {}
void ArtemisTopExecutionListener::executed(ExecutableConfiguration* conf, const ExecutionResult* result) {}
void ArtemisTopExecutionListener::loaded_page(const ArtemisWebPage& page) {}
void ArtemisTopExecutionListener::script_crash(QString cause) {}
void ArtemisTopExecutionListener::artemis_finished() {}
void ArtemisTopExecutionListener::eval_called(QString eval_string) {}
void ArtemisTopExecutionListener::code_loaded(QString source, QUrl url, int startline) {}

}
