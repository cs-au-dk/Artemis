#ifndef AJAXREQUESTLISTENER_H
#define AJAXREQUESTLISTENER_H
#include <QNetworkAccessManager>
#include <QUrl>
namespace artemis
{



class AjaxRequestListener : public QNetworkAccessManager
{
    Q_OBJECT
public:
    explicit AjaxRequestListener(QObject* parent = 0);
    QNetworkReply* createRequest(Operation op, const QNetworkRequest& req, QIODevice* outgoingData = 0);

signals:
    void pageGet(QUrl url);
    void pagePost(QUrl url);
public slots:

};

}
#endif // AJAXREQUESTLISTENER_H
