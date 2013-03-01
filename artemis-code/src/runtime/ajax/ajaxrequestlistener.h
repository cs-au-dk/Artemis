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
