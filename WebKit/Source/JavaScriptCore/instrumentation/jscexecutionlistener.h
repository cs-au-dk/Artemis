#ifdef ARTEMIS
#ifndef JSCEXECUTIONLISTENER_H
#define JSCEXECUTIONLISTENER_H

namespace JSC {
class UString;
}

namespace jsinst {


class JSCExecutionListener
{
public:
    JSCExecutionListener();
    virtual void jsc_eval_call(const char * eval_string);
};



void initialize_js_listener(JSCExecutionListener* l);
JSCExecutionListener* get_js_listener();

}
#endif // JSCEXECUTIONLISTENER_H
#endif
