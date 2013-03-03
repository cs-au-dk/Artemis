/*
 * Copyright 2012 Aarhus University
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
#include <QtWebKit>
#include <QEventLoop>
#include <QNetworkRequest>
#include <QNetworkReply>
#include <QObject>
#include <QTextStream>

#include "urlutil.h"

namespace artemis
{

QUrl resolveUrl(const QUrl& base, const QString& relative)
{
    QUrl u(relative);

    if (!u.isRelative())
        { return u; }

    return base.resolved(u);
}

void makeScriptUrlsAbsolute(QWebFrame* page)
{
    QWebElementCollection scripts = page->findAllElements("script");
    foreach(QWebElement script, scripts) {
        if (script.hasAttribute("src")) { //External element
            QString src = script.attribute("src");
            QUrl absUrl = resolveUrl(page->url(), src);
            script.setAttribute("src", absUrl.toString());
        }
    }
}

QString readEntirePage(const QUrl& page)
{
    QNetworkAccessManager netAccess;

    QUrl curl = page;
    QNetworkReply* reply = netAccess.get(QNetworkRequest(QUrl(curl)));
    QEventLoop loop;
    QObject::connect(reply, SIGNAL(readyRead()), &loop, SLOT(quit()));
    loop.exec();
    QTextStream q(reply->readAll());
    return q.readAll();
}

QString readEntirePage(const QUrl& page, const QString postData)
{
    QNetworkAccessManager netAccess;

    QUrl curl = page;
    QNetworkReply* reply = netAccess.post(QNetworkRequest(QUrl(curl)), postData.toAscii());
    QEventLoop loop;
    QObject::connect(reply, SIGNAL(readyRead()), &loop, SLOT(quit()));
    loop.exec();
    QTextStream q(reply->readAll());
    return q.readAll();

}

/**
  Given url a/b/c/ will return a/b if no / is present. Returns .
  */
QString getPathPartOfUrl(const QString url)
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
QString getFilenamePartOfUrl(const QString& url)
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
QUrl toRelative(QUrl base, QUrl absolute)
{
    QStringList sBase = base.toString().split("/");
    QStringList sAbsolute = absolute.toString().split("/");
    QStringList res = QStringList(sAbsolute);

    if (base.isParentOf(absolute)) {
        foreach(QString s, sBase) {
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
}
