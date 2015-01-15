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

#include <QString>
#include <QDebug>

#include <qhttpserver.h>
#include <qhttprequest.h>
#include <qhttpresponse.h>
#include <qjson/parser.h>

#include "util/loggingutil.h"

#include "analysisserverruntime.h"

namespace artemis
{

AnalysisServerRuntime::AnalysisServerRuntime(QObject* parent, const Options& options, const QUrl& url)
    : Runtime(parent, options, url)
{
    QHttpServer *server = new QHttpServer(this);
    connect(server, SIGNAL(newRequest(QHttpRequest*, QHttpResponse*)),
            this, SLOT(handleRequest(QHttpRequest*, QHttpResponse*)));
    server->listen(QHostAddress::Any, 8099);
}

void AnalysisServerRuntime::run(const QUrl &url)
{
    QJson::Parser parser;
    bool ok;

    QString json = "{\"test\":\"message\", \"other\":[\"hello\", \"goodbye\"]}";

    QVariant result = parser.parse(json.toUtf8(), &ok);

    if (!ok) {
        Log::fatal("Error in parsing JSON");
        exit(1);
    }

    qDebug() << result;

    Log::fatal("Analysis Server Runtime not yet implemented");
    //exit(1);
}


void AnalysisServerRuntime::handleRequest(QHttpRequest *request, QHttpResponse *response)
{
    QByteArray body = "Hello World\n";
    response->setHeader("Content-Length", QString::number(body.size()));
    response->writeHead(200);
    response->end(body);
}





} // namespace artemis
