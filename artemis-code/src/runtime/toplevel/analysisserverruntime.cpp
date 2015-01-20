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
    , mServerState(IDLE)
{
    // Connections to the server part
    QObject::connect(&mAnalysisServer, SIGNAL(sigExecuteCommand(CommandPtr)),
                     this, SLOT(slExecuteCommand(CommandPtr)));
    QObject::connect(this, SIGNAL(sigCommandFinished(QVariant)),
                     &mAnalysisServer, SLOT(slCommandFinished(QVariant)));
    QObject::connect(&mAnalysisServer, SIGNAL(sigResponseFinished()),
                     this, SLOT(slResponseFinished()));

    // Connections to the brpwser part
    QObject::connect(mWebkitExecutor, SIGNAL(sigExecutedSequence(ExecutableConfigurationConstPtr, QSharedPointer<ExecutionResult>)),
                     this, SLOT(slExecutedSequence(ExecutableConfigurationConstPtr,QSharedPointer<ExecutionResult>)));
    QObject::connect(mWebkitExecutor->getPage().data(), SIGNAL(sigNavigationRequest(QWebFrame*,QNetworkRequest,QWebPage::NavigationType)),
                     this, SLOT(slNavigationRequest(QWebFrame*,QNetworkRequest,QWebPage::NavigationType)));
    mWebkitExecutor->getPage()->mAcceptNavigation = false;
}

void AnalysisServerRuntime::run(const QUrl &url)
{
    Log::info("Analysis Server Runtime waiting for messages...");
}

void AnalysisServerRuntime::slExecuteCommand(CommandPtr command)
{
    Log::debug("  Analysis server runtime: recieved new command.");

    mCurrentCommand = command;

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

    mServerState = EXIT;

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

    mServerState = PAGELOAD;
    loadUrl(command->url); // Calls back to slExecutedSequence.
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
    if (mServerState == EXIT) {
        // Hack: Wait a little so the response can be sent out (non-blocking on networking).
        DelayUtil::delay(1000);
        done();
    }

    mServerState = IDLE;
    mCurrentCommand.clear();
}


// TODO: Very similar method used in demowindow.cpp
void AnalysisServerRuntime::loadUrl(QUrl url)
{
    mWebkitExecutor->getPage()->mAcceptNavigation = true;

    ExecutableConfigurationPtr noInput = ExecutableConfigurationPtr(new ExecutableConfiguration(InputSequencePtr(new InputSequence()), url));
    mWebkitExecutor->executeSequence(noInput, MODE_CONCOLIC_CONTINUOUS); // Calls slExecutedSequence method as callback.
}

void AnalysisServerRuntime::slExecutedSequence(ExecutableConfigurationConstPtr configuration, QSharedPointer<ExecutionResult> result)
{
    // For now the only state where we expect to be executing a sequence is when loading a page.
    // TODO: Replace this with a switch on which state we are in.
    assert(mServerState == PAGELOAD);

    mWebkitExecutor->getPage()->mAcceptNavigation = false; // Now the loading is finished and further navigation must be dealt with via slNavigationRequest.

    // TODO: Save the configuration and result so they can be used by other commands.

    // Send a response and finish the PAGELOAD command.
    QVariantMap response;
    response.insert("pageload", "done");

    emit sigCommandFinished(response);
}

// Called when the ArtemisWebPage receives a request for navigation and we have set it's mAcceptingNavigation flag to false.
// i.e. when we want to intercept the load and pass it to WebkitExecutor instead.
// This is done to make sure that all navigation (including "implicit" navigation like clicking links) is handled via WebKitExecutor.
void AnalysisServerRuntime::slNavigationRequest(QWebFrame *frame, const QNetworkRequest &request, QWebPage::NavigationType type)
{
    loadUrl(request.url());
}




} // namespace artemis
