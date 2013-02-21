#ifdef ARTEMIS

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
    cerr << "ERROR: Default listener for javascript_eval_call was invoked, args: " << eval_string << endl;
    exit(1);
}

void JSCExecutionListener::javascript_bytecode_executed(CodeBlock* codeBlock, Instruction* inst) {
    cerr << "ERROR: Default listener for javascript_bytecode_executed was invoked " << endl;
    exit(1);
}

void JSCExecutionListener::javascript_constant_encountered(std::string constant) {
    cerr << "ERROR: Default listener for javascript_constant_encountered was invoked " << endl;
    exit(1);
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
