#ifndef MULTIPLEXLISTENER_H
#define MULTIPLEXLISTENER_H

#include "artemistopexecutionlistener.h"
#include <QList>
#include <cstdarg>

namespace artemis {

class MultiplexListener : public ArtemisTopExecutionListener
{
public:
    MultiplexListener(int number_of_listners, ...);
    void before_execute(ExecutableConfiguration* conf);
    void executed(ExecutableConfiguration* conf, const ExecutionResult* result);
    void loaded_page(const ArtemisWebPage& page);
    void script_crash(QString cause);
    void artemis_finished();
    void add_listener(ArtemisTopExecutionListener* l);
    void artemis_start(const QUrl& url);
    void code_loaded(QString source, QUrl url, int startline);

private:
    QList<ArtemisTopExecutionListener*> m_listeners;
};

}

#endif // MULTIPLEXLISTENER_H
