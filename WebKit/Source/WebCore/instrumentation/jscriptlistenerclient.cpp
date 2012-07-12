#ifdef ARTEMIS
#include "jscriptlistenerclient.h"

namespace inst {

JScriptListenerClient::JScriptListenerClient(ExecutionListener* l)
{
    this->owner = l;
}

void JScriptListenerClient::jsc_eval_call(const char * eval_string) {
    owner->webkit_eval_call(eval_string);
}

}
#endif
