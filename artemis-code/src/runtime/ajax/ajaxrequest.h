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

    bool operator ==(const AjaxRequest &other) const;
    QDebug friend operator<<(QDebug dbg, const AjaxRequest &e);
    uint hashcode() const;

private:
    QString m_post_data;
    QUrl m_url;
};

}

inline uint qHash(const artemis::AjaxRequest &key) {
    return key.hashcode();
}
#endif // AJAXREQUEST_H
