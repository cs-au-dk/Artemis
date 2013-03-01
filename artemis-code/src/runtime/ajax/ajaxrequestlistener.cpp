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
