#include "multiplexlistener.h"

namespace artemis {

MultiplexListener::MultiplexListener(int number_of_listners, ...)
{
    va_list ap;
    int i = 0;
    ArtemisTopExecutionListener* l;
    va_start(ap,number_of_listners);
    while (i < number_of_listners) {
         l = va_arg(ap,ArtemisTopExecutionListener*);
         this->m_listeners.append(l);
         i++;
    }
    va_end(ap);
}

void MultiplexListener::before_execute(ExecutableConfiguration* conf) {
    foreach (ArtemisTopExecutionListener* l, m_listeners) {
        l->before_execute(conf);
    }
}

void MultiplexListener::executed(ExecutableConfiguration* conf, const ExecutionResult* result) {
    foreach (ArtemisTopExecutionListener* l, m_listeners) {
        l->executed(conf, result);
    }
}

void MultiplexListener::loaded_page(const ArtemisWebPage& page) {
    foreach (ArtemisTopExecutionListener* l, m_listeners) {
        l->loaded_page(page);
    }
}

void MultiplexListener::script_crash(QString cause) {
    foreach (ArtemisTopExecutionListener* l, m_listeners) {
        l->script_crash(cause);
    }
}

void MultiplexListener::artemis_finished() {
    foreach (ArtemisTopExecutionListener* l, m_listeners) {
        l->artemis_finished();
    }
}

void MultiplexListener::artemis_start(const QUrl& url) {
    foreach (ArtemisTopExecutionListener* l, m_listeners) {
        l->artemis_start(url);
    }
}

void MultiplexListener::code_loaded(QString source, QUrl url, int startline) {
    foreach (ArtemisTopExecutionListener* l, m_listeners) {
        //qDebug() << "MWAH: "  << QString::number((int)l) << " ! " << source << " ! " << url << " sdfg " << m_listeners.size();
        l->code_loaded (source,url,startline);
    }
}

void MultiplexListener::add_listener(ArtemisTopExecutionListener* l) {
    this->m_listeners.append(l);
}

}
