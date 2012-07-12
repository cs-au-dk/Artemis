#ifndef DOMSTATESAVERLISTENER_H
#define DOMSTATESAVERLISTENER_H

#include "listeners/artemistopexecutionlistener.h"
#include <QtNetwork/QNetworkAccessManager>
#include <QtNetwork/QNetworkReply>
#include <QSet>

namespace artemis {

class DOMStateSaverListener : public ArtemisTopExecutionListener
{
public:
    DOMStateSaverListener(QString path);
    ~DOMStateSaverListener();
    void executed(const ExecutableConfiguration& conf, const ExecutionResult& result);
    void loaded_page(const ArtemisWebPage& page);
    void artemis_finished();

private:
    void create_index();

    QString save_to_path;
    QString initial_url_state;
    QString state_after_onload;
    int iter;
    bool did_dump_url_state;
    QNetworkAccessManager net_access;
    QSet<QString> created_html_files;
};

}
#endif // DOMSTATESAVERLISTENER_H
