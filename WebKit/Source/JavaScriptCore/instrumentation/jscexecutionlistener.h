#ifdef ARTEMIS
#ifndef JSCEXECUTIONLISTENER_H
#define JSCEXECUTIONLISTENER_H

namespace JSC {
    class CodeBlock;
    class Instruction;
    class ExecState;
}


namespace jscinst {

class JSCExecutionListener
{

public:
    JSCExecutionListener();
    virtual void javascript_eval_call(const char * eval_string); //__attribute__((noreturn));
    virtual void javascript_bytecode_executed(JSC::CodeBlock*, JSC::Instruction* inst); //__attribute__((noreturn));
    virtual void javascript_constant_encountered(std::string constant); //__attribute__((noreturn));
    virtual void javascript_property_read(std::string propertyName, JSC::ExecState*); //__attribute__((noreturn));
    virtual void javascript_property_written(std::string propertyName, JSC::ExecState*); //__attribute__((noreturn));
};

extern JSCExecutionListener* jsc_listener;

void register_jsc_listener(JSCExecutionListener* listener);
JSCExecutionListener* get_jsc_listener();

}

#endif // JSCEXECUTIONLISTENER_H
#endif
