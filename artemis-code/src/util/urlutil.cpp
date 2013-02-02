#include <QtWebKit>
#include <QEventLoop>
#include <QNetworkRequest>
#include <QNetworkReply>
#include <QObject>
#include <QTextStream>

#include "urlutil.h"

namespace artemis
{

QUrl resolve_url(const QUrl& base, const QString& relative)
{
    QUrl u(relative);

    if (!u.isRelative())
        { return u; }

    return base.resolved(u);
}

void make_script_urls_absolute(QWebFrame* page)
{
    QWebElementCollection scripts = page->findAllElements("script");
    foreach(QWebElement script, scripts) {
        if (script.hasAttribute("src")) { //External element
            QString src = script.attribute("src");
            QUrl abs_url = resolve_url(page->url(), src);
            script.setAttribute("src", abs_url.toString());
        }
    }
}

QString read_entire_page(const QUrl& page)
{
    QNetworkAccessManager net_access;

    QUrl curl = page;
    QNetworkReply* reply = net_access.get(QNetworkRequest(QUrl(curl)));
    QEventLoop loop;
    QObject::connect(reply, SIGNAL(readyRead()), &loop, SLOT(quit()));
    loop.exec();
    QTextStream q(reply->readAll());
    return q.readAll();
}

QString read_entire_page(const QUrl& page, const QString post_data)
{
    QNetworkAccessManager net_access;

    QUrl curl = page;
    QNetworkReply* reply = net_access.post(QNetworkRequest(QUrl(curl)), post_data.toAscii());
    QEventLoop loop;
    QObject::connect(reply, SIGNAL(readyRead()), &loop, SLOT(quit()));
    loop.exec();
    QTextStream q(reply->readAll());
    return q.readAll();

}

/**
  Given url a/b/c/ will return a/b if no / is present. Returns .
  */
QString get_path_part_of_url(const QString url)
{
    if (!url.contains("/"))
        { return "."; }

    QStringList parts = url.split("/");
    parts.removeLast();
    return parts.join("/");
}

/**
  Given url a/b/c will return c, if no / is present returns string unchanged
  */
QString get_filename_part_of_url(const QString& url)
{
    if (!url.contains("/"))
        { return url; }

    QStringList parts = url.split("/");
    return parts.last();
}

/**
  Given base url http://host.com/a and aboslute url http://host.com/a/b/c return the best effort relative url
    b/c
  */
QUrl to_relative(QUrl base, QUrl absolute)
{
    QStringList s_base = base.toString().split("/");
    QStringList s_absolute = absolute.toString().split("/");
    QStringList res = QStringList(s_absolute);

    if (base.isParentOf(absolute)) {
        foreach(QString s, s_base) {
            res.removeFirst();
        }
    }
    else {
        //Chop of the domain part
        res.removeFirst();
        res.removeFirst();
        res.removeFirst();
    }

    return res.join("/");
}

int get_hash(const QUrl& u, int startline)
{
    return qHash(u) * 53 + startline * 29;
}
}
