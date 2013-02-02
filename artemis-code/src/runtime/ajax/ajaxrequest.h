#ifndef AJAXREQUEST_H
#define AJAXREQUEST_H

#include <QString>
#include <QUrl>
#include <QDebug>

namespace artemis
{

class AjaxRequest
{
public:
    AjaxRequest(const QUrl url, const QString postData);

    QUrl url() const;
    QString postData();

    QDebug friend operator<<(QDebug dbg, const AjaxRequest& e);

private:
    QString mPostData;
    QUrl mUrl;
};

}

#endif // AJAXREQUEST_H
