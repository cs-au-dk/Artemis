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

#include <assert.h>
#include <qhttpserver.h>
#include <qhttprequest.h>
#include <qhttpresponse.h>
#include <qjson/parser.h>

#include "requesthandler.h"
#include "responsehandler.h"

#include "util/loggingutil.h"

#include "analysisserver.h"

namespace artemis
{

AnalysisServer::AnalysisServer(quint16 port)
    : mBusy(0)
{
    mServer = new QHttpServer(this);
    QObject::connect(mServer, SIGNAL(newRequest(QHttpRequest*, QHttpResponse*)),
                     this, SLOT(slHandleRequest(QHttpRequest*, QHttpResponse*)));
    mServer->listen(QHostAddress::Any, port);

    Log::debug("AnalysisServer listening...");
}

AnalysisServer::~AnalysisServer()
{
    Log::debug("Closing AnalysisServer");
    if (mServer) {
        mServer->close();
        delete mServer;
    }
}

void AnalysisServer::slHandleRequest(QHttpRequest* request, QHttpResponse* response)
{
    // Set the busy flag. This server is blocking and requires synchronous requests.
    if (mBusy.testAndSetAcquire(0, 1)) {
        // Create a request handler object which will wait for all the data to be received and build a Command object.
        // Once this is done it will callback to the slNewCommand slot and delete itself, so we don't need to save it.
        Log::debug("Request recieved...");
        waitingResponse = response;
        new RequestHandler(request, response, this);

    } else {
        Log::debug("Request recieved... but I'm busy.");
        rejectWhenBusy(request, response);
    }
}

// Send an error response while the server is busy with a different request.
void AnalysisServer::rejectWhenBusy(QHttpRequest *request, QHttpResponse *response)
{
    QVariantMap message;
    message.insert("error", "Server is busy.");

    ResponseHandler::sendResponse(response, message);
}

void AnalysisServer::slNewCommand(CommandPtr command)
{
    Log::debug("  Analysis server: recieved new command.");

    // For now there is no queue of commands as this server is blocking.
    // Just pass this straight on to the runtime.
    emit sigExecuteCommand(command);
}

void AnalysisServer::slCommandFinished(QVariant response)
{
    Log::debug("  Analysis server: Finished executing command.");

    // If the command is finished, send the response and then mark this server as idle and ready for a new command.
    assert(waitingResponse);
    ResponseHandler::sendResponse(waitingResponse, response);

    Log::debug("  Analysis server: Response sent, server is idle again.");

    bool releasedOk = mBusy.testAndSetRelease(1, 0);
    assert(releasedOk);
}

} // namespace artemis

