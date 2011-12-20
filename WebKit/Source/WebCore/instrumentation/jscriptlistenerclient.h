#ifdef ARTEMIS
#ifndef JSCRIPTLISTENERCLIENT_H
#define JSCRIPTLISTENERCLIENT_H

#include "executionlistener.h"
#include "../JavaScriptCore/instrumentation/jscexecutionlistener.h"

namespace inst {

class JScriptListenerClient : public jsinst::JSCExecutionListener
{
public:
    JScriptListenerClient(ExecutionListener* l);
    virtual void jsc_eval_call(const char * eval_string);

private:
    ExecutionListener* owner;
};

}
#endif // JSCRIPTLISTENERCLIENT_H
#endif
