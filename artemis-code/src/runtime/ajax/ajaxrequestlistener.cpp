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
        { emit this->pageGet(req.url()); }
    else if (op == PostOperation)
        { emit this->pagePost(req.url()); }

    return reply;
}

}
