#ifndef URLUTIL_H
#define URLUTIL_H

#include <QUrl>
#include <QWebFrame>

namespace artemis {
    QUrl resolve_url(const QUrl& base, const QString& realtive);
    void make_script_urls_absolute(QWebFrame* page);
    QString read_entire_page(const QUrl& page);
    QString read_entire_page(const QUrl& page, const QString post_data);
    QString get_path_part_of_url(const QString url);
    QString get_filename_part_of_url(const QString& url);
    QUrl to_relative(QUrl base, QUrl absolute);
    int get_hash(const QUrl& u, int startline);


}

#endif // URLUTIL_H
