/*
 * Copyright 2012 Aarhus University
 *
 * Licensed under the GNU General Public License, Version 3 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *          http://www.gnu.org/licenses/gpl-3.0.html
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <qhttpserver.h>
#include <qhttprequest.h>
#include <qhttpresponse.h>
#include <qjson/parser.h>

#include "analysisserver.h"

namespace artemis
{

AnalysisServer::AnalysisServer(quint16 port)
{
    mServer = new QHttpServer(this);
    QObject::connect(mServer, SIGNAL(newRequest(QHttpRequest*, QHttpResponse*)),
                     this, SLOT(handleRequest(QHttpRequest*, QHttpResponse*)));
    mServer->listen(QHostAddress::Any, port);
}

AnalysisServer::~AnalysisServer()
{
    if (mServer) {
        mServer->close();
        delete mServer;
    }
}

void AnalysisServer::handleRequest(QHttpRequest* request, QHttpResponse* response)
{
    QByteArray body = "Hello World\n";
    response->setHeader("Content-Length", QString::number(body.size()));
    response->writeHead(200);
    response->end(body);
}


} // namespace artemis

