#include <QList>
#include <QNetworkCookie>
#include <QDebug>
#include "immutablecookiejar.h"

namespace artemis {

    ImmutableCookieJar::ImmutableCookieJar(const QMap<QString,QString> &initialstate, const QString &domain)
        : QNetworkCookieJar()
    {
        foreach(QString key, initialstate.keys()) {
            QNetworkCookie * cookie = new QNetworkCookie(key.toAscii(), initialstate[key].toAscii());
            cookie->setPath(QString("/"));
            cookie->setDomain(domain);
            m_cookies.append(*cookie);
        }
        this->setAllCookies(m_cookies);
    }

    QList<QNetworkCookie> ImmutableCookieJar::cookiesForUrl(const QUrl &url) const {
        return m_cookies;
    }

    bool ImmutableCookieJar::setCookiesFromUrl(const QList<QNetworkCookie> &cookieList, const QUrl &url)
    {
        return true;
    }

}
