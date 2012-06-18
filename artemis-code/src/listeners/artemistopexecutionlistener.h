#ifndef ARTEMISTOPEXECUTIONLISTENER_H
#define ARTEMISTOPEXECUTIONLISTENER_H

#include <QtWebKit>

#include "runtime/executableconfiguration.h"
#include "runtime/browser/executionresult.h"
#include "runtime/browser/artemiswebpage.h"

namespace artemis {

    class ArtemisTopExecutionListener
    {
    public:
        ArtemisTopExecutionListener();
        virtual void artemis_start(const QUrl& url);
        virtual void before_execute(ExecutableConfiguration* conf);
        virtual void executed(ExecutableConfiguration* conf, const ExecutionResult& result);
        virtual void loaded_page(const ArtemisWebPage& page);
        virtual void script_crash(QString cause);
        virtual void artemis_finished();
        virtual void eval_called(QString eval_string);
        virtual void code_loaded(QString source, QUrl url, int startline);
    };

}
#endif // ARTEMISTOPEXECUTIONLISTENER_H
