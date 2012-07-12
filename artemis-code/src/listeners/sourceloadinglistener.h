#ifndef SOURCELOADINGLISTENER_H
#define SOURCELOADINGLISTENER_H

#include <QUrl>
#include <QSet>
#include <QPair>

#include <listeners/artemistopexecutionlistener.h>

namespace artemis {

class SourceLoadingListener : public ArtemisTopExecutionListener
{
public:
    SourceLoadingListener();
    void code_loaded(QString source, QUrl url, int startline);
    void loaded_page(const ArtemisWebPage& page);
    void print_results();

private:
    //Set of url + startline hash
    QSet<int> visisted;
    QMap<int, QPair<QUrl,int> > locs;
    //Map from hash to size in bytes;
    QMap<int,unsigned int> size_of_code;
    QMap<QString,QString> rewrite_urls;
    int src_idx;
    int file_idx;
};

}

#endif // SOURCELOADINGLISTENER_H
