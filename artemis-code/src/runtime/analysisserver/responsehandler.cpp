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
#include <QStringList>

#include <qjson/serializer.h>

#include "util/loggingutil.h"

#include "responsehandler.h"

namespace artemis
{

void ResponseHandler::sendResponse(QHttpResponse* response, QByteArray data)
{
    Log::debug("  Response handler: Sending response:");
    foreach (QString line, QString(data).split("\n")) {
        Log::debug(QString("    %1").arg(line).toStdString());
    }

    response->setHeader("Content-Length", QString::number(data.size()));
    response->writeHead(200);
    response->end(data);
    // QHttpResponse deletes itself, so there is no cleaning up to be done.
}

void ResponseHandler::sendResponse(QHttpResponse *response, QVariant data)
{
    QJson::Serializer serializer;
    bool ok;

    QByteArray json = serializer.serialize(data, &ok);

    if (!ok) {
        QVariantMap message;
        message.insert("error", "Could not encode response to JSON.");

        json = serializer.serialize(message);
    }

    sendResponse(response, json);
}



} // namespace artemis
