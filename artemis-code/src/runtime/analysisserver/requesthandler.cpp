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

#include <QStringList>

#include <qhttprequest.h>
#include <qhttpresponse.h>

#include "requesthandler.h"

namespace artemis
{

RequestHandler::RequestHandler(QHttpRequest* request, QHttpResponse* response, AnalysisServer *server)
    : mRequest(request)
    , mResponse(response)
{
    // Set up callback back to server.
    QObject::connect(this, SIGNAL(sigNewCommand(CommandPtr)),
                     server, SLOT(slNewCommand(CommandPtr)));

    // Let this object be deleted once the response is handled.
    QObject::connect(mResponse, SIGNAL(done()),
                     this, SLOT(deleteLater()));

    // Notify the server once this response is finished.
    QObject::connect(mResponse, SIGNAL(done()),
                     server, SLOT(slResponseFinished()));

    // Just save the request and response and wait while any POST data arrives.

    // Have the request store its own body data. Then we only have to wait for the done() signal, not every data().
    mRequest->storeBody();

    QObject::connect(mRequest, SIGNAL(end()),
                     this, SLOT(slRequestFullyLoaded()));

    Log::debug("  Request handler: ready");

}

RequestHandler::~RequestHandler()
{
    delete mRequest;
    // mResponse deletes itself once it is finished with.
}

void RequestHandler::slRequestFullyLoaded()
{
    Log::debug("  Request handler: finished loading request.");

    Log::debug("  Data is:");
    foreach (QString line, QString(mRequest->body()).split("\n")) {
        Log::debug(QString("    %1").arg(line).toStdString());
    }

    // Now we have all the request data, we can parse it and build a Command object.
    CommandPtr command = createCommand(parseBody(mRequest->body()));

    emit sigNewCommand(command);
}

QVariant RequestHandler::parseBody(QByteArray body)
{
    QJson::Parser parser;
    bool ok;

    QVariant result = parser.parse(body, &ok);

    if (!ok) {
        Log::debug("  Request handler: JSON parse error.");
        return QVariant(); // 'Invalid' QVariant.
    }

    Log::debug("  Request handler: JSON parsed OK.");
    return result;
}

CommandPtr RequestHandler::createCommand(QVariant data)
{
    // If 'data' is not valid, then there was an error in parsing the JSON.
    if (!data.isValid()) {
        return parseError("Could not parse the JSON request.");
    }

    // Check the top-level object is a map.
    if (data.type() != QVariant::Map) {
        return parseError("Top-level structure in the JSON request is expected to be an object.");
    }

    QVariantMap mainObject = data.toMap();

    // Pull out the command.
    if (!mainObject.contains("command")) {
        return parseError("Could not find the \"command\" field in the top-level object.");
    }

    QString command = mainObject["command"].toString();

    // For each command, pull out the other relevant data.
    if (command == "exit") {
        return exitCommand(mainObject);

    } else if (command == "echo") {
        return echoCommand(mainObject);

    } else if (command == "pageload") {
        return pageloadCommand(mainObject);

    } else {
        return parseError("Command was not recognised.");
    }

}

CommandPtr RequestHandler::parseError(QString message)
{
    Log::debug(QString("  Request handler: Parse error: %1").arg(message).toStdString());
    return ErrorCommandPtr(new ErrorCommand(message));
}

CommandPtr RequestHandler::exitCommand(QVariantMap mainObject)
{
    Log::debug("  Request handler: Building Exit command.");

    // There are no extra fields to fetch for an exit command.
    return ExitCommandPtr(new ExitCommand());
}

CommandPtr RequestHandler::echoCommand(QVariantMap mainObject)
{
    Log::debug("  Request handler: Building Echo command.");

    // Fetch the message
    if (!mainObject.contains("message")) {
        return parseError("Could not find the \"message\" property for an echo command.");
    }

    if (mainObject["message"].type() != QVariant::String) {
        return parseError("The \"message\" property for an echo command must be a string.");
    }

    uint delay = 0;
    if (mainObject.contains("delay")) {
        bool ok;
        delay = mainObject["delay"].toUInt(&ok); // Will convert a string "5" to integer 5.
        if (!ok) {
            return parseError("The \"delay\" property for an echo command must be a positive integer.");
        }
        if (delay > 30) {
            return parseError("The \"delay\" property must be at most 30 seconds.");
        }
    }

    return EchoCommandPtr(new EchoCommand(mainObject["message"].toString(), delay));
}

CommandPtr RequestHandler::pageloadCommand(QVariantMap mainObject)
{
    Log::debug("  Request handler: Building PageLoad command.");

    // Fetch the URL and validate it
    if (!mainObject.contains("url")) {
        return parseError("Could not find the \"url\" property for a pageload command.");
    }

    if (mainObject["url"].type() != QVariant::String) {
        return parseError("The \"url\" property for a pageload command must be a string.");
    }

    // URL is assumed to be unencoded and parsed in tolerant mode.
    QUrl url(mainObject["url"].toString());

    if (!url.isValid()) {
        return parseError("Invalid \"url\" property for a pageload command.");
    }

    return PageLoadCommandPtr(new PageLoadCommand(url));
}


}
