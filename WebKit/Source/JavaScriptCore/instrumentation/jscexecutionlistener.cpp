#ifdef ARTEMIS

#include <iostream>
#include <cstdlib>

#include "jscexecutionlistener.h"

using namespace std;

namespace jscinst {

JSCExecutionListener::JSCExecutionListener()
{
}

void JSCExecutionListener::javascript_eval_call(const char* eval_string) {
    cerr << "Warning: Default listener for javascript_eval_call was invoked, args: " << eval_string << endl;
    //exit(1);
}

void JSCExecutionListener::javascript_bytecode_executed(JSC::CodeBlock*, JSC::Instruction*) {
    cerr << "Warning: Default listener for javascript_bytecode_executed was invoked " << endl;
    //exit(1);
}

void JSCExecutionListener::javascript_constant_encountered(std::string) {
    cerr << "Warning: Default listener for javascript_constant_encountered was invoked " << endl;
    //exit(1);
}

void JSCExecutionListener::javascript_property_read(std::string, JSC::ExecState*)
{
    cerr << "Warning: Default listener for javascript_property_read was invoked " << endl;
    //exit(1);
}

void JSCExecutionListener::javascript_property_written(std::string, JSC::ExecState*)
{
    cerr << "Warning: Default listener for javascript_property_written was invoked " << endl;
    //exit(1);
}

JSCExecutionListener* jsc_listener = 0;

void register_jsc_listener(JSCExecutionListener* listener) {
    jsc_listener = listener;
}

JSCExecutionListener* get_jsc_listener() {
    if (jsc_listener == 0) {
        jsc_listener = new JSCExecutionListener();
    }
    return jsc_listener;
}

}
#endif
