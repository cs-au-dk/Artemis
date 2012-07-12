#ifndef URLCOLLECTOR_H
#define URLCOLLECTOR_H

#include <QUrl>
#include <QSet>
#include <QDebug>

class URLCollector
{
public:
    URLCollector();
    QSet<QUrl> get_urls();
    void add_url(QUrl url);
    void print_urls() const;
    QDebug friend operator<<(QDebug dbg, const URLCollector &e);

private:
    QSet<QUrl> m_urls;
};

#endif // URLCOLLECTOR_H
