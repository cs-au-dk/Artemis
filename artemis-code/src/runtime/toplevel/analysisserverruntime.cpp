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

#include <qjson/parser.h>

#include "util/loggingutil.h"
#include "util/delayutil.h"

#include "analysisserverruntime.h"

namespace artemis
{

AnalysisServerRuntime::AnalysisServerRuntime(QObject* parent, const Options& options, const QUrl& url)
    : Runtime(parent, options, url)
    , mAnalysisServer(options.analysisServerPort)
    , mWaitingToExit(false)
{
    QObject::connect(&mAnalysisServer, SIGNAL(sigExecuteCommand(CommandPtr)),
                     this, SLOT(slExecuteCommand(CommandPtr)));

    QObject::connect(this, SIGNAL(sigCommandFinished(QVariant)),
                     &mAnalysisServer, SLOT(slCommandFinished(QVariant)));

    QObject::connect(&mAnalysisServer, SIGNAL(sigResponseFinished()),
                     this, SLOT(slResponseFinished()));
}

void AnalysisServerRuntime::run(const QUrl &url)
{
    Log::info("Analysis Server Runtime waiting for messages...");
}

void AnalysisServerRuntime::slExecuteCommand(CommandPtr command)
{
    Log::debug("  Analysis server runtime: recieved new command.");

    // Recieved a new command from the AnalysisServer.
    // Execute it (calls back the appropriate execute() method).
    command->accept(this);
}

void AnalysisServerRuntime::execute(Command* command)
{
    Log::debug("  Analysis server runtime: executing a generic command (error).");
    assert(command);

    emit sigCommandFinished(errorResponse("Executing an unimplemented command."));
}

void AnalysisServerRuntime::execute(ExitCommand* command)
{
    Log::debug("  Analysis server runtime: executing an exit command.");
    assert(command);

    QVariantMap response;
    response.insert("message", "Server is shutting down");

    mWaitingToExit = true;

    emit sigCommandFinished(response);
}

void AnalysisServerRuntime::execute(ErrorCommand* command)
{
    Log::debug("  Analysis server runtime: executing an error command.");
    assert(command);

    // This means there was some error in the parsing.
    // Just pass the error through and return it.
    emit sigCommandFinished(errorResponse(command->message));
}

void AnalysisServerRuntime::execute(EchoCommand* command)
{
    Log::debug("  Analysis server runtime: executing an echo command.");
    assert(command);

    QVariantMap response;
    response.insert("message", command->message);

    if (command->delay > 0) {
        DelayUtil::delay(command->delay * 1000);
    }

    emit sigCommandFinished(response);
}

void AnalysisServerRuntime::execute(PageLoadCommand* command)
{
    Log::debug("  Analysis server runtime: executing a pageload command.");
    assert(command);

    emit sigCommandFinished(errorResponse("Page load command is not yet implemented."));
}

QVariant AnalysisServerRuntime::errorResponse(QString message)
{
    QVariantMap response;
    response.insert("error", message);
    return response;
}


// Called once the response from an execute() method has been sent.
void AnalysisServerRuntime::slResponseFinished()
{
    Log::debug("  Analysis server runtime: Response is complete.");
    if (mWaitingToExit) {
        // Hack: Wait a little so the response can be sent out (non-blocking on networking).
        DelayUtil::delay(1000);
        done();
    }
}



} // namespace artemis
