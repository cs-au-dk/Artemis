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
#include <QVariant>

#include <qjson/parser.h>

#include "util/loggingutil.h"
#include "util/delayutil.h"
#include "runtime/input/forms/formfieldinjector.h"

#include "analysisserverruntime.h"

namespace artemis
{

AnalysisServerRuntime::AnalysisServerRuntime(QObject* parent, const Options& options, const QUrl& url)
    : Runtime(parent, options, url)
    , mAnalysisServer(options.analysisServerPort)
    , mServerState(IDLE)
    , mIsPageLoaded(false)
    , mIsScheduledRedirection(false)
    , mFieldReadLog(mWebkitExecutor->getPage())
{
    // Connections to the server part
    QObject::connect(&mAnalysisServer, SIGNAL(sigExecuteCommand(CommandPtr)),
                     this, SLOT(slExecuteCommand(CommandPtr)));
    QObject::connect(this, SIGNAL(sigCommandFinished(QVariant)),
                     &mAnalysisServer, SLOT(slCommandFinished(QVariant)));
    QObject::connect(&mAnalysisServer, SIGNAL(sigResponseFinished()),
                     this, SLOT(slResponseFinished()));

    // Connections to the browser part
    QObject::connect(mWebkitExecutor, SIGNAL(sigExecutedSequence(ExecutableConfigurationConstPtr, QSharedPointer<ExecutionResult>)),
                     this, SLOT(slExecutedSequence(ExecutableConfigurationConstPtr,QSharedPointer<ExecutionResult>)));

    QObject::connect(mWebkitExecutor->getPage().data(), SIGNAL(sigNavigationRequest(QWebFrame*,QNetworkRequest,QWebPage::NavigationType)),
                     this, SLOT(slNavigationRequest(QWebFrame*,QNetworkRequest,QWebPage::NavigationType)));
    mWebkitExecutor->getPage()->mAcceptNavigation = false;

    QObject::connect(mWebkitExecutor->mWebkitListener, SIGNAL(sigPageLoadScheduled(QUrl)),
                     this, SLOT(slPageLoadScheduled(QUrl)));

    // Connections for page analysis
    QObject::connect(QWebExecutionListener::getListener(), SIGNAL(sigJavascriptSymbolicFieldRead(QString, bool)),
                     &mFieldReadLog, SLOT(slJavascriptSymbolicFieldRead(QString, bool)));

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

    // The whole load process is limited by the timeout field.
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

    // Group the handlers by element.
    // It is safe to use the xpaths as keys because we generate them ourselves, so they are canonical and we cannot
    // have two different xpaths referring to the same element.
    QMap<QString, QList<QVariant> > elementHandlers;
    foreach (EventHandlerDescriptorConstPtr handler, handlerList) {
        elementHandlers[handler->xPathOrTargetObject()].append(handler->getName());
    }

    QVariantList resultList;
    foreach (QString identifier, elementHandlers.keys()) {
        QVariantMap handlerObject;
        handlerObject.insert("element", identifier);
        handlerObject.insert("events", elementHandlers[identifier]);
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
        emit sigCommandFinished(errorResponse("The XPath did not match any elements."));
        return;
    }
    if (count > 1) {
        emit sigCommandFinished(errorResponse(QString("The XPath did not match a unique element. There were %1 matching elements.").arg(count)));
        return;
    }

    // N.B. The XPath provided here is used as part of the event descriptor to decide which events are duplicates.
    // So unless we create a "canonical" XPath here, different XPaths pointing to the same element will be considered
    // different events by FieldReadLog. It's an API decision about whether canonical XPaths are best or returning the
    // XPath given is best (the current decision).
    mFieldReadLog.beginEvent("click", command->xPath);

    // Execute the click.
    QString clickJS = QString("document.evaluate(\"%1\", document, null, XPathResult.UNORDERED_NODE_SNAPSHOT_TYPE, null).snapshotItem(0).click();").arg(escapedXPath);
    document.evaluateJavaScript(clickJS);

    QVariantMap result;
    result.insert("click", "done");

    emit sigCommandFinished(result);
}

void AnalysisServerRuntime::execute(PageStateCommand *command)
{
    Log::debug("  Analysis server runtime: executing a Page-State command.");
    assert(command);

    // Check we have loaded a page already.
    if (!mIsPageLoaded) {
        emit sigCommandFinished(errorResponse("Cannot execute page command until a page is loaded."));
        return;
    }

    QString url = mWebkitExecutor->getPage()->mainFrame()->url().toString();
    QString title = mWebkitExecutor->getPage()->mainFrame()->title();
    QString dom = mWebkitExecutor->getPage()->mainFrame()->toHtml();
    uint domEltCount = mWebkitExecutor->getPage()->mainFrame()->documentElement().findAll("*").count();
    uint domCharCount = dom.length();

    QVariantMap result;
    result.insert("url", url);
    result.insert("title", title);
    if (command->includeDom) {
        result.insert("dom", dom);
    }
    result.insert("elements", domEltCount);
    result.insert("characters", domCharCount);

    emit sigCommandFinished(result);
}

void AnalysisServerRuntime::execute(ElementCommand *command)
{
    Log::debug("  Analysis server runtime: executing an element info command.");
    assert(command);

    // Check we have loaded a page already.
    if (!mIsPageLoaded) {
        emit sigCommandFinished(errorResponse("Cannot execute element command until a page is loaded."));
        return;
    }

    // Look up the element(s).
    QWebElement document = mWebkitExecutor->getPage()->currentFrame()->documentElement();
    QString escapedXPath = command->xPath;
    escapedXPath.replace('"', "\\\"");
    QString queryJS = QString("var elems = document.evaluate(\"%1\", document, null, XPathResult.UNORDERED_NODE_SNAPSHOT_TYPE, null); var elStrs = []; for(var i=0; i < elems.snapshotLength; i++) {elStrs.push(elems.snapshotItem(i).outerHTML)}; elStrs;").arg(escapedXPath);

    QVariant elemList = document.evaluateJavaScript(queryJS);

    if(!elemList.isValid()) {
        emit sigCommandFinished(errorResponse("Invalid XPath."));
        return;
    }

    QVariantMap result;
    result.insert("elements", elemList);

    emit sigCommandFinished(result);
}

void AnalysisServerRuntime::execute(FieldsReadCommand *command)
{
    Log::debug("  Analysis server runtime: executing a Fields-Read command.");
    assert(command);

    // Check we have loaded a page already.
    if (!mIsPageLoaded) {
        emit sigCommandFinished(errorResponse("Cannot execute fieldsread command until a page is loaded."));
        return;
    }

    QVariantMap result;
    result.insert("fieldsread", mFieldReadLog.getLog());

    emit sigCommandFinished(result);
}

void AnalysisServerRuntime::execute(BackButtonCommand *command)
{
    Log::debug("  Analysis server runtime: executing a Back-button command.");
    assert(command);

    // Check we have loaded a page already.
    if (!mIsPageLoaded) {
        emit sigCommandFinished(errorResponse("Cannot execute backbutton command until a page is loaded."));
        return;
    }

    backButtonOrError(); // Calls back to slExecutedSequence or finishes the request itself.
}

void AnalysisServerRuntime::execute(FormInputCommand *command)
{
    Log::debug("  Analysis server runtime: executing a Form-input command.");
    assert(command);

    // Check we have loaded a page already.
    if (!mIsPageLoaded) {
        emit sigCommandFinished(errorResponse("Cannot execute forminput command until a page is loaded."));
        return;
    }

    // Look up the element.
    QWebElement field = mWebkitExecutor->getPage()->getElementByXPath(command->field);
    if (field.isNull()) {
        emit sigCommandFinished(errorResponse("Form-input field could not be found. The XPath either did not match or matched multiple elements."));
        return;
    }

    // Sanity check that this element is a form field and the injection value is an appropriate type.
    // Some of these checks are repeated in FormFieldInjector::inject, but doing them here allows us to give sensible
    // error messages, which is useful seeing as this command has quite specific requirements.
    Log::debug(QString("    Checking field \"%1\" can accept value %2").arg(field.tagName(), command->value.toString()).toStdString());
    if (field.tagName().toLower() == "input") {
        // For input fields, the allowable value type depends on the inupt type.
        // "radio" and "checkbox" inputs must have bool values, and all other input types must use "string".
        QString inputType = field.attribute("type").toLower();
        if (inputType == "checkbox" || inputType == "radio") {
            if (command->value.getType() != QVariant::Bool) {
                emit sigCommandFinished(errorResponse(QString("Only boolean values can be injected into inputs with 'checkbox' or 'radio' type.")));
                return;
            }
        } else if (command->value.getType() != QVariant::String) {
            emit sigCommandFinished(errorResponse(QString("Only string values can be injected into normal input fields.")));
            return;
        }
    } else if (field.tagName().toLower() == "select") {
        // For select boxes we support injection of string or int (as selectedIndex) but not bool.
        if (command->value.getType() != QVariant::String && command->value.getType() != QVariant::Int) {
            emit sigCommandFinished(errorResponse(QString("Could not inject '%1' into a select box. Only strings and integers (for selectedIndex) are supported.").arg(command->value.toString())));
            return;
        }
    } else {
        emit sigCommandFinished(errorResponse(QString("Could not inject into element '%1'; only 'input' or 'select' supported.").arg(field.tagName())));
        return;
    }

    // Inject
    bool couldInject = FormFieldInjector::inject(field, command->value);
    if (!couldInject) {
        // Hopefully all these case will already be caught by the sanity-check code above...
        emit sigCommandFinished(errorResponse(QString("Failed to inject value %1 into field %2.").arg(command->value.toString(), command->field)));
        return;
    }

    // Trigger the change handler.
    FormFieldInjector::triggerChangeHandler(field);

    // Done, nothing to return.
    QVariantMap result;
    result.insert("forminput", "done");

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

// Use the back button.
// Either calls back to slExecutedSequence or emits the commandFinished signal with an error response.
void AnalysisServerRuntime::backButtonOrError()
{
    // Check if there is any history to go back to.
    if (mWebkitExecutor->getPage()->history()->canGoBack()) {
        mServerState = PAGELOAD_BACK_BUTTON;
        mWebkitExecutor->getPage()->history()->back(); // Calls back to slExecutedSequence.

    } else {
        emit sigCommandFinished(errorResponse("No more history to go back through."));
    }
}

void AnalysisServerRuntime::slExecutedSequence(ExecutableConfigurationConstPtr configuration, QSharedPointer<ExecutionResult> result)
{
    PageLoadCommandPtr loadCommand; // PAGELOAD_BLANK
    QVariantMap response; // PAGELOAD
    QString url; // PAGELOAD_BACK_BUTTON

    switch (mServerState) {
    case PAGELOAD_BLANK:
        // We are part way through the page-load process. Now we are ready to load the target URL.
        loadCommand = mCurrentCommand.dynamicCast<PageLoadCommand>();
        assert(loadCommand);

        mServerState = PAGELOAD;
        mIsScheduledRedirection = false;

        mFieldReadLog.clear();
        mFieldReadLog.beginEvent("pageload", "");

        loadUrl(loadCommand->url); // Calls back to slExecutedSequence again.
        break;

    case PAGELOAD:
        // Successfully finished loading the real URL.
        mWebkitExecutor->getPage()->mAcceptNavigation = false; // Now the loading is finished any further navigation must be dealt with via slNavigationRequest.

        // Check for any redirection we detected.
        if (mIsScheduledRedirection) {
            // Wait for the redirected page load to come in...
            mServerState = PAGELOAD_WAITING_REDIRECT;

        } else {
            // Send a response and finish the PAGELOAD command.
            mIsPageLoaded = true;
            response.insert("pageload", "done");
            response.insert("url", mWebkitExecutor->getPage()->currentFrame()->url().toString());

            emit sigCommandFinished(response);
        }
        break;

    case PAGELOAD_TIMEOUT:
        emitTimeout();
        break;

    case PAGELOAD_WAITING_REDIRECT:
        // Do not check for more redirects here to avoid going into a loop.

        // Send a response and finish the PAGELOAD command.
        response.insert("pageload", "done");
        response.insert("url", mWebkitExecutor->getPage()->currentFrame()->url().toString());

        emit sigCommandFinished(response);

        break;

    case PAGELOAD_BACK_BUTTON:
        // Do not support redirection when using the back button.

        // If we have reached "about:blank" then this is one of the intermediate loads between pageload commands.
        // In that case issue another back command to mask this.
        // TODO: This is a bit of a hack to pretend we do not do these intermediate loads.
        // It could be tripped up if someone intentionally loads "about:blank" and tries to go back to it.
        // It also causes some odd behaviour when going back from the initial page load (the result is "about:blank"
        // loaded and an error response).

        url = mWebkitExecutor->getPage()->currentFrame()->url().toString();
        if (url == "about:blank") {
            backButtonOrError(); // Calls back to slExecutedSequence or finishes the request itself.

        } else {
            // Send a response and finish the backbutton command.
            response.insert("backbutton", "done");
            response.insert("url", url);

            emit sigCommandFinished(response);
        }

        break;

    case IDLE:
        // This is an unexpected page load.
        // It could be caused by a page redirect.
        // Other navigation (e.g. clicking links) is supposed to be handled via slNavigationRequest and loadUrl.

        // There is nothing to do (as the server already thought the page loading was complete), so silently proceed.
        // TODO: If there was any per-page analysis state, it should be reset here as well. All we have so far is the
        // mFieldReadLog, which we want to start logging from the initial call to pageload, so this is not reset.

        break;

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

// Called when a page load is scheduled.
// This is used to detect meta-refresh redirection during a page load command.
void AnalysisServerRuntime::slPageLoadScheduled(QUrl url)
{
    mIsScheduledRedirection = true;
}

// Overrides Runtime::slAbortedExecution, called from WebkitExecutor when there is a problem with executing a sequence.
void AnalysisServerRuntime::slAbortedExecution(QString reason)
{
    if (mServerState == PAGELOAD ||
            mServerState == PAGELOAD_BLANK ||
            mServerState == PAGELOAD_WAITING_REDIRECT ||
            mServerState == PAGELOAD_BACK_BUTTON) {
        // There was an error loading this page.
        emit sigCommandFinished(errorResponse("Could not load the URL."));

    } else if (mServerState == PAGELOAD_TIMEOUT) {
        emitTimeout();

    } else {
        Runtime::slAbortedExecution(reason);
    }
}




} // namespace artemis
