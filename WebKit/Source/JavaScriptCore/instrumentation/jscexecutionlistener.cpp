#ifdef ARTEMIS
#include <iostream>

#include "jscexecutionlistener.h"

using namespace JSC;
using namespace std;

namespace jsinst {

JSCExecutionListener* js_executionlistener = 0;

JSCExecutionListener::JSCExecutionListener()
{
}

void JSCExecutionListener::jsc_eval_call(const char * eval_string) {
    cout << "WARNING: Default listener for jsc_eval_call was invoked, args: " << eval_string << endl;
}

void initialize_js_listener(JSCExecutionListener* l) {
    jsinst::js_executionlistener = l;
}

JSCExecutionListener* get_js_listener() {
    if (jsinst::js_executionlistener == 0)
        jsinst::js_executionlistener = new JSCExecutionListener();
    return jsinst::js_executionlistener;
}

}
#endif
