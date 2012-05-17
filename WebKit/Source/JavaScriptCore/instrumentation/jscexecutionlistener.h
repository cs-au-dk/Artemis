#ifdef ARTEMIS
#ifndef JSCEXECUTIONLISTENER_H
#define JSCEXECUTIONLISTENER_H

namespace JSC {
    class UString;
    class CodeBlock;
    class Instruction;
}


namespace jsinst {


class JSCExecutionListener
{
public:
    JSCExecutionListener();
    virtual void jsc_eval_call(const char * eval_string);
    void listen_byte_code_executed(JSC::CodeBlock*, JSC::Instruction* inst);
    virtual void jsc_bytecode_executed(const char * url, unsigned int linenumber, int bytecode_offset, int opcodeID);
};



void initialize_js_listener(JSCExecutionListener* l);
JSCExecutionListener* get_js_listener();

}
#endif // JSCEXECUTIONLISTENER_H
#endif
