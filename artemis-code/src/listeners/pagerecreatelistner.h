#ifndef PAGERECREATELISTNER_H
#define PAGERECREATELISTNER_H

#include <QString>
#include <QDir>
#include <QSet>

#include "listeners/artemistopexecutionlistener.h"

namespace artemis {

class PageRecreateListner : public ArtemisTopExecutionListener
{
public:
    PageRecreateListner();
    void artemis_start(const QUrl& url);
    void loaded_page(const ArtemisWebPage& page);
    void executed(const ExecutableConfiguration& conf, const ExecutionResult* result);
    void code_loaded(QString source, QUrl url, int startline);

private:
    QDir base_dir;
    QUrl base_url;
    QSet<QUrl> ajax_urls_fetched;
    //Set of url + startline hash
    QSet<int> script_urls_fetched;
};

}
#endif // PAGERECREATELISTNER_H
