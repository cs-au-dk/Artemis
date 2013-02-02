#ifndef IMMUTABLECOOKIEJAR_H_
#define IMMUTABLECOOKIEJAR_H_

#include <QMap>
#include <QList>
#include <QString>
#include <QNetworkCookieJar>
#include <QNetworkCookie>

namespace artemis
{

class ImmutableCookieJar : public QNetworkCookieJar
{
public:
    ImmutableCookieJar(const QMap<QString, QString> &initialstate, const QString& domain);
    bool setCookiesFromUrl(const QList<QNetworkCookie> &cookieList, const QUrl& url);
    QList<QNetworkCookie> cookiesForUrl(const QUrl& url) const;

protected:
private:
    QList<QNetworkCookie> m_cookies;
};

}
#endif /* IMMUTABLECOOKIEJAR_H_ */
