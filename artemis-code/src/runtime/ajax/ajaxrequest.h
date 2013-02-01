#ifndef AJAXREQUEST_H
#define AJAXREQUEST_H

#include <QString>
#include <QUrl>
#include <QDebug>

namespace artemis {

class AjaxRequest
{
public:
    AjaxRequest(const QUrl url, const QString post_data);

    QUrl url() const;
    QString post_data();

    QDebug friend operator<<(QDebug dbg, const AjaxRequest &e);

private:
    QString m_post_data;
    QUrl m_url;
};

}

#endif // AJAXREQUEST_H
