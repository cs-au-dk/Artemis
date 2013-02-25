#ifndef URLUTIL_H
#define URLUTIL_H

#include <QUrl>
#include <QWebFrame>

namespace artemis
{
QUrl resolveUrl(const QUrl& base, const QString& realtive);
void makeScriptUrlsAbsolute(QWebFrame* page);
QString readEntirePage(const QUrl& page);
QString readEntirePage(const QUrl& page, const QString postData);
QString getPathPartOfUrl(const QString url);
QString getFilenamePartOfUrl(const QString& url);
QUrl toRelative(QUrl base, QUrl absolute);


}

#endif // URLUTIL_H
