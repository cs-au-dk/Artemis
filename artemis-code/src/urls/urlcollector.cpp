#include "urlcollector.h"
#include <iostream>

using namespace std;

URLCollector::URLCollector()
{
}

QSet<QUrl> URLCollector::get_urls() {
    return m_urls;
}

void URLCollector::add_url(QUrl url) {
    this->m_urls << url;
}

QDebug operator<<(QDebug dbg, const URLCollector &e) {
    dbg.nospace() << e.m_urls;
    return dbg.space();
}

void URLCollector::print_urls() const {
    foreach(QUrl u, this->m_urls) {
        cout << u.toString().toStdString() << endl;
    }
}
