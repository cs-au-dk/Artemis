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

#include <QDateTime>

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

AnalysisServer::AnalysisServer(quint16 port, bool log)
    : mBusy(0)
    , mLogging(log)
    , mLogFile("server-log.txt")
    , mLogStream(&mLogFile)
{
    mServer = new QHttpServer(this);
    QObject::connect(mServer, SIGNAL(newRequest(QHttpRequest*, QHttpResponse*)),
                     this, SLOT(slHandleRequest(QHttpRequest*, QHttpResponse*)));
    bool boundToPort = mServer->listen(QHostAddress::Any, port);

    if (!boundToPort) {
        Log::fatal(QString("AnalysisServer could not bind to port %1.").arg(port).toStdString());
        exit(1);
    }

    QObject::connect(&mResponseHandler, SIGNAL(sigServerLog(QString, bool)),
                     this, SLOT(slServerLog(QString, bool)));

    if (mLogging) {
        if (mLogFile.open(QIODevice::WriteOnly | QIODevice::Truncate | QIODevice::Text)) {
            logEntry("Server started.");
        } else {
            Log::error("Could not open server log for writing.");
            mLogging = false;
        }
    }

    Log::debug("AnalysisServer listening...");
}

AnalysisServer::~AnalysisServer()
{
    Log::debug("Closing AnalysisServer");
    if (mServer) {
        mServer->close();
        delete mServer;
    }
    if (mLogging) {
        mLogFile.close();
    }
}

void AnalysisServer::slHandleRequest(QHttpRequest* request, QHttpResponse* response)
{
    // Set the busy flag. This server is blocking and requires synchronous requests.
    if (mBusy.testAndSetAcquire(0, 1)) {
        // Create a request handler object which will wait for all the data to be received and build a Command object.
        // Once this is done it will callback to the slNewCommand slot and delete itself, so we don't need to save it.
        Log::debug("Request recieved...");
        mWaitingResponse = response;
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

    mResponseHandler.sendResponse(response, message);
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

    assert(mWaitingResponse);
    mResponseHandler.sendResponse(mWaitingResponse, response);
}

void AnalysisServer::slResponseFinished()
{
    // The response has finished sending
    emit sigResponseFinished();

    // Mark the server as idle and ready for a new command.
    bool releasedOk = mBusy.testAndSetRelease(1, 0);
    assert(releasedOk);

    Log::debug("  Analysis server: Response sent, server is idle again.");
}


void AnalysisServer::slServerLog(QString data, bool direction)
{
    data.replace("\n", "\n    ");
    QString message = QString("%1:\n    %2").arg(direction ? "Sent" : "Received").arg(data);
    logEntry(message);
}

void AnalysisServer::logEntry(QString message)
{
    if (mLogging) {
        QString date = QDateTime::currentDateTime().toString("yyyy-MM-dd hh-mm-ss");
        mLogStream << QString("[%1] %2\n").arg(date).arg(message);
        mLogStream.flush();
    }
}

} // namespace artemis

