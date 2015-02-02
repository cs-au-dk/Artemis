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
#include <QTimer>

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
    , mIsPageLoaded(false)
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

    mIsPageLoaded = false;

    // The whole load process is limited by the timout field.
    if (command->timeout > 0) {
        QTimer::singleShot(command->timeout, this, SLOT(slLoadTimeoutTriggered()));
    }

    // WebkitExecutor uses the contents of the page to check for a successful load or not.
    // Therefore this check fails if we are already on a non-blank page.
    // So the first step of a page load is to load "about:blank", and then load the "real" URL.

    mServerState = PAGELOAD_BLANK;
    loadUrl(QUrl("about:blank")); // Calls back to slExecutedSequence.
}

void AnalysisServerRuntime::execute(HandlersCommand *command)
{
    Log::debug("  Analysis server runtime: executing a handlers command.");
    assert(command);

    // Retrieve the list of handlers from the saved response from the previous page load.
    if (!mIsPageLoaded) {
        emit sigCommandFinished(errorResponse("Handlers cannot be listed until a page is loaded."));
        return;
    }

    QList<EventHandlerDescriptorConstPtr> handlerList = mWebkitExecutor->getCurrentEventHandlers();
    QVariantList resultList;
    foreach (EventHandlerDescriptorConstPtr handler, handlerList) {
        QVariantMap handlerObject;
        handlerObject.insert("event", handler->getName());
        handlerObject.insert("element", handler->xPathToElement());
        resultList.append(handlerObject);
    }

    QVariantMap result;
    result.insert("handlers", resultList);

    emit sigCommandFinished(result);
}

void AnalysisServerRuntime::execute(ClickCommand *command)
{
    Log::debug("  Analysis server runtime: executing a click command.");
    assert(command);

    // Check we have loaded a page already.
    if (!mIsPageLoaded) {
        emit sigCommandFinished(errorResponse("Cannot execute click command until a page is loaded."));
        return;
    }

    // Look up the element
    QWebElement document = mWebkitExecutor->getPage()->currentFrame()->documentElement();
    QString escapedXPath = command->xPath;
    escapedXPath.replace('"', "\\\"");
    QString countingJS = QString("document.evaluate(\"%1\", document, null, XPathResult.UNORDERED_NODE_SNAPSHOT_TYPE, null).snapshotLength;").arg(escapedXPath);
    uint count = document.evaluateJavaScript(countingJS).toUInt();
    if (count == 0) {
        emit sigCommandFinished( errorResponse("The XPath did not match any elements."));
        return;
    }
    if (count > 1) {
        emit sigCommandFinished(errorResponse(QString("The XPath did not match a unique element. There were %1 matching elements.").arg(count)));
        return;
    }

    // Execute the click.
    QString clickJS = QString("document.evaluate(\"%1\", document, null, XPathResult.UNORDERED_NODE_SNAPSHOT_TYPE, null).snapshotItem(0).click();").arg(escapedXPath);
    document.evaluateJavaScript(clickJS);

    QVariantMap result;
    result.insert("click", "done");

    emit sigCommandFinished(result);
}

void AnalysisServerRuntime::execute(DomCommand *command)
{
    Log::debug("  Analysis server runtime: executing a DOM listing command.");
    assert(command);

    // Check we have loaded a page already.
    if (!mIsPageLoaded) {
        emit sigCommandFinished(errorResponse("Cannot execute dom command until a page is loaded."));
        return;
    }

    QString dom = mWebkitExecutor->getPage()->mainFrame()->toHtml();

    QVariantMap result;
    result.insert("dom", dom);

    emit sigCommandFinished(result);
}

QVariant AnalysisServerRuntime::errorResponse(QString message)
{
    QVariantMap response;
    response.insert("error", message);
    return response;
}

void AnalysisServerRuntime::emitTimeout()
{
    emit sigCommandFinished(errorResponse("Timed out."));
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
    PageLoadCommandPtr loadCommand; // PAGELOAD_BLANK
    QVariantMap response; // PAGELOAD

    switch (mServerState) {
    case PAGELOAD_BLANK:
        // We are part way through the page-load process. Now we are ready to load the target URL.
        loadCommand = mCurrentCommand.dynamicCast<PageLoadCommand>();
        assert(loadCommand);
        mServerState = PAGELOAD;
        loadUrl(loadCommand->url); // Calls back to slExecutedSequence again.
        break;

    case PAGELOAD:
        // Successfully finished loading the real URL.
        mWebkitExecutor->getPage()->mAcceptNavigation = false; // Now the loading is finished any further navigation must be dealt with via slNavigationRequest.

        // Send a response and finish the PAGELOAD command.
        mIsPageLoaded = true;
        response.insert("pageload", "done");
        response.insert("url", mWebkitExecutor->getPage()->currentFrame()->url().toString());

        emit sigCommandFinished(response);
        break;

    case PAGELOAD_TIMEOUT:
        emitTimeout();
        break;

    case IDLE: // Fall-through
    case EXIT: // Fall-through
    default:
        // We do not expect any other server states to be executing event sequences.
        Log::fatal("Error: Executed an event sequence from a bad state in AnalysisServerRuntime.");
        exit(1);
        break;
    }
}

void AnalysisServerRuntime::slLoadTimeoutTriggered()
{
    mServerState = PAGELOAD_TIMEOUT;
    mWebkitExecutor->getPage()->triggerAction(QWebPage::Stop);
    // slExecutedSequence will now be called.
}

// Called when the ArtemisWebPage receives a request for navigation and we have set it's mAcceptingNavigation flag to false.
// i.e. when we want to intercept the load and pass it to WebkitExecutor instead.
// This is done to make sure that all navigation (including "implicit" navigation like clicking links) is handled via WebKitExecutor.
void AnalysisServerRuntime::slNavigationRequest(QWebFrame *frame, const QNetworkRequest &request, QWebPage::NavigationType type)
{
    loadUrl(request.url());
}

// Overrides Runtime::slAbortedExecution, called from WebkitExecutor when there is a problem with executing a sequence.
void AnalysisServerRuntime::slAbortedExecution(QString reason)
{
    if (mServerState == PAGELOAD) {
        // There was an error loading this page.
        emit sigCommandFinished(errorResponse("Could not load the URL."));

    } else if (mServerState == PAGELOAD_TIMEOUT) {
        emitTimeout();

    } else {
        Runtime::slAbortedExecution(reason);
    }
}




} // namespace artemis
