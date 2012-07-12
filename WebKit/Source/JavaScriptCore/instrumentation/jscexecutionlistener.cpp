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

namespace jsinst {

JSCExecutionListener* js_executionlistener = 0;

JSCExecutionListener::JSCExecutionListener()
{
}

void JSCExecutionListener::jsc_eval_call(const char * eval_string) {
    cout << "WARNING: Default listener for jsc_eval_call was invoked, args: " << eval_string << endl;
}

void JSCExecutionListener::listen_byte_code_executed(CodeBlock* codeBlock, Instruction* inst) {
    int offset  = inst -  codeBlock->instructions().begin();
    jsc_bytecode_executed(codeBlock->source()->url().utf8(false).data(),
                          codeBlock->lineNumberForBytecodeOffset(offset),
                          offset,
                          -1); //TODO: Find out how to get the opcode from WebKit
}

void JSCExecutionListener::jsc_bytecode_executed(const char * url, unsigned int linenumber, int bytecode_offset, int opcodeID) {
    //cout << "WARNING: Default listener for jsc_bytecode_executed was invoked " << endl;
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
