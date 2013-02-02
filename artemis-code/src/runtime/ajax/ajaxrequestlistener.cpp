#include "ajaxrequestlistener.h"
#include <QNetworkAccessManager>
#include <QNetworkRequest>


namespace artemis
{

AjaxRequestListener::AjaxRequestListener(QObject* parent) :
    QNetworkAccessManager(parent)
{
}

QNetworkReply* AjaxRequestListener::createRequest(Operation op, const QNetworkRequest& req, QIODevice* outgoingData)

{
    //super call
    QNetworkReply* reply = QNetworkAccessManager::createRequest(op, req, outgoingData);

    if (op == GetOperation)
        { emit this->page_get(req.url()); }
    else if (op == PostOperation)
        { emit this->page_post(req.url()); }

    return reply;
}

}
