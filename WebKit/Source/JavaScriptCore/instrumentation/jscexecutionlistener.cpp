#ifdef ARTEMIS

#include <assert.h>
#include <iostream>

#include "jscexecutionlistener.h"
#include "config.h"
#include "Interpreter.h"

#include "Arguments.h"
#include "BatchedTransitionOptimizer.h"
#include "CallFrame.h"
#include "CallFrameClosure.h"
#include "bytecode/CodeBlock.h"
#include "bytecode/Instruction.h"

using namespace JSC;
using namespace std;

namespace jscinst {

JSCExecutionListener::JSCExecutionListener()
{
}

void JSCExecutionListener::javascript_eval_call(const char * eval_string) {
    cout << "ERROR: Default listener for javascript_eval_call was invoked, args: " << eval_string << endl;
    assert(false);
}

void JSCExecutionListener::javascript_bytecode_executed(CodeBlock* codeBlock, Instruction* inst) {
    cout << "ERROR: Default listener for javascript_bytecode_executed was invoked " << endl;
    assert(false);
}

void JSCExecutionListener::javascript_constant_encountered(std::string constant) {
    cout << "ERROR: Default listener for javascript_constant_encountered was invoked " << endl;
    assert(false);
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
