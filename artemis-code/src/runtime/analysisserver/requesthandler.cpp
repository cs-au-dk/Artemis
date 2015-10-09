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
        return parseError("Could not find the 'command' field in the top-level object.");
    }

    QString command = mainObject["command"].toString();

    QStringList expectedFields;
    CommandPtr cmdObject;

    // For each command, pull out the other relevant data.
    if (command == "exit") {
        expectedFields = QStringList();
        cmdObject = exitCommand(mainObject);

    } else if (command == "echo") {
        expectedFields = QStringList() << "message" << "delay";
        cmdObject = echoCommand(mainObject);

    } else if (command == "pageload") {
        expectedFields = QStringList() << "url" << "timeout";
        cmdObject = pageloadCommand(mainObject);

    } else if (command == "handlers") {
        expectedFields = QStringList() << "filter";
        cmdObject = handlersCommand(mainObject);

    } else if (command == "click") {
        expectedFields = QStringList() << "element" << "method";
        cmdObject = clickCommand(mainObject);

    } else if (command == "dom") {
        return parseError("The 'dom' command is no longer supported; it has been replaced by the 'page' command.");

    } else if (command == "page") {
        expectedFields = QStringList() << "dom";
        cmdObject = pageCommand(mainObject);

    } else if (command == "element") {
        expectedFields = QStringList() << "element" << "property";
        cmdObject = elementCommand(mainObject);

    } else if (command == "fieldsread") {
        expectedFields = QStringList();
        cmdObject = fieldsReadCommand(mainObject);

    } else if (command == "backbutton") {
        expectedFields = QStringList();
        cmdObject = backbuttonCommand(mainObject);

    } else if (command == "forminput") {
        expectedFields = QStringList() << "field" << "value" << "method" << "noblur";
        cmdObject = forminputCommand(mainObject);

    } else if (command == "xpath") {
        expectedFields = QStringList() << "xpath";
        cmdObject = xpathCommand(mainObject);

    } else if (command == "event") {
        expectedFields = QStringList() << "element" << "event";
        cmdObject = eventCommand(mainObject);

    } else if (command == "windowsize") {
        expectedFields = QStringList() << "width" << "height";
        cmdObject = windowsizeCommand(mainObject);

    } else if (command == "concolicadvice") {
        expectedFields = QStringList() << "action" << "sequence" << "amount";
        cmdObject = concolicAdviceCommand(mainObject);

    } else {
        return parseError("Command was not recognised.");
    }

    // If there were unexpected fields in the request, return an error.
    QStringList unexpected = unexpectedFields(expectedFields, mainObject);
    if (!unexpected.empty()) {
        return unexpectedFieldsError(command, unexpected);
    }

    return cmdObject;
}

CommandPtr RequestHandler::parseError(QString message)
{
    Log::debug(QString("  Request handler: Parse error: %1").arg(message).toStdString());
    return ErrorCommandPtr(new ErrorCommand(message));
}

QStringList RequestHandler::unexpectedFields(QStringList expected, QVariantMap mainObject)
{
    QStringList error;
    expected.append("command");

    foreach(QString key, mainObject.keys()) {
        if (!expected.contains(key)) {
            error.append(key);
        }
    }

    return error;
}

CommandPtr RequestHandler::unexpectedFieldsError(QString command, QStringList unexpected)
{
    assert(unexpected.length() > 0);
    return parseError(QString("Unexpected field%1 '%2' in '%3' command.")
                      .arg(unexpected.length() > 1 ? "s" : "")
                      .arg(unexpected.join("', '"))
                      .arg(command));
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
        return parseError("Could not find the 'message' property for an echo command.");
    }

    if (mainObject["message"].type() != QVariant::String) {
        return parseError("The 'message' property for an echo command must be a string.");
    }

    uint delay = 0;
    if (mainObject.contains("delay")) {
        bool ok;
        delay = mainObject["delay"].toUInt(&ok); // Will convert a string "5" to integer 5.
        if (!ok) {
            return parseError("The 'delay' property for an echo command must be a positive integer.");
        }
        if (delay > 30) {
            return parseError("The 'delay' property must be at most 30 seconds.");
        }
    }

    return EchoCommandPtr(new EchoCommand(mainObject["message"].toString(), delay));
}

CommandPtr RequestHandler::pageloadCommand(QVariantMap mainObject)
{
    Log::debug("  Request handler: Building PageLoad command.");

    // Fetch the URL and validate it
    if (!mainObject.contains("url")) {
        return parseError("Could not find the 'url' property for a pageload command.");
    }

    if (mainObject["url"].type() != QVariant::String) {
        return parseError("The 'url' property for a pageload command must be a string.");
    }

    // URL is assumed to be unencoded and parsed in tolerant mode.
    QUrl url(mainObject["url"].toString());

    if (!url.isValid()) {
        return parseError("Invalid 'url' property for a pageload command.");
    }

    uint timeout = 0;
    if (mainObject.contains("timeout")) {
        bool ok;
        timeout = mainObject["timeout"].toUInt(&ok); // Will convert a string "5" to integer 5.
        if (!ok) {
            return parseError("The 'timeout property for a pageload command must be a positive integer.");
        }
        if (timeout > 3600000) {
            return parseError("The 'timeout' property must be at most 3,600,000 milliseconds.");
        }
    }

    return PageLoadCommandPtr(new PageLoadCommand(url, timeout));
}

CommandPtr RequestHandler::handlersCommand(QVariantMap mainObject)
{
    Log::debug("  Request handler: Building Handlers command.");

    // There is an optional "filter" field.
    QString filter; // Default to null string if not supplied.
    if (mainObject.contains("filter")) {
        if (mainObject["filter"].type() != QVariant::String) {
            return parseError("The 'filter' property for a handlers command must be a string.");
        }
        filter = mainObject["filter"].toString();
    }

    return HandlersCommandPtr(new HandlersCommand(filter));
}

CommandPtr RequestHandler::clickCommand(QVariantMap mainObject)
{
    Log::debug("  Request handler: Building Click command.");

    // Fetch the XPath
    if (!mainObject.contains("element")) {
        return parseError("Could not find the 'element' property for a click command.");
    }

    if (mainObject["element"].type() != QVariant::String) {
        return parseError("The 'element' property for a click command must be a string.");
    }

    // There may be an optional 'method' entry.
    ClickCommand::ClickSimulationMethod method = ClickCommand::Simple; // By default use a single click event.
    QString methodRequested = "simple";
    if (mainObject.contains("method")) {
        if (mainObject["method"].type() != QVariant::String) {
            return parseError("The 'method' property for a 'click' command must be a string.");
        }

        methodRequested = mainObject["method"].toString();
        if (methodRequested == "simple") {
            method = ClickCommand::Simple;
        } else if (methodRequested == "simulate-js") {
            method = ClickCommand::SimulateJS;
        } else if (methodRequested == "simulate-gui") {
            method = ClickCommand::SimulateGUI;
        } else {
            return parseError("The 'method' property for a 'click' command must be one of 'simple', 'simulate-js' or 'simulate-gui'.");
        }
    }

    return ClickCommandPtr(new ClickCommand(mainObject["element"].toString(), method, methodRequested));
}

CommandPtr RequestHandler::pageCommand(QVariantMap mainObject)
{
    Log::debug("  Request handler: Building Page-State command.");

    // There is an optional 'dom' field, which defaults to false if not present.
    bool includeDom = false;
    if (mainObject.contains("dom")) {
        if (mainObject["dom"].type() != QVariant::Bool) {
            return parseError("The 'dom' property for a page command must be a boolean.");
        }
        includeDom = mainObject["dom"].toBool();
    }

    return PageStateCommandPtr(new PageStateCommand(includeDom));
}

CommandPtr RequestHandler::elementCommand(QVariantMap mainObject)
{
    Log::debug("  Request handler: Building element info command.");

    // Fetch the XPath
    if (!mainObject.contains("element")) {
        return parseError("Could not find the 'element' property for an element command.");
    }

    if (mainObject["element"].type() != QVariant::String) {
        return parseError("The 'element' property for an element command must be a string.");
    }

    // There is an optional "property" field.
    QString property; // Default to null string if not supplied.
    if (mainObject.contains("property")) {
        if (mainObject["property"].type() != QVariant::String) {
            return parseError("The 'property' property for an element command must be a string.");
        }
        property = mainObject["property"].toString();
    }

    return ElementCommandPtr(new ElementCommand(mainObject["element"].toString(), property));
}

CommandPtr RequestHandler::fieldsReadCommand(QVariantMap mainObject)
{
    Log::debug("  Request handler: Building Fields-Read command.");

    // There are no extra fields to fetch for a fieldsread command.
    return FieldsReadCommandPtr(new FieldsReadCommand());
}

CommandPtr RequestHandler::backbuttonCommand(QVariantMap mainObject)
{
    Log::debug("  Request handler: Building Back-button command.");

    // There are no extra fields to fetch for a backbutton command.
    return BackButtonCommandPtr(new BackButtonCommand());
}

CommandPtr RequestHandler::forminputCommand(QVariantMap mainObject)
{
    Log::debug("  Request handler: Building Form-input command.");

    // There should be a 'field' entry (string) and a 'value' entry (string or bool).
    if (!mainObject.contains("field")) {
        return parseError("Could not find the 'field' property for a forminput command.");
    }

    if (mainObject["field"].type() != QVariant::String) {
        return parseError("The 'field' property for a forminput command must be a string.");
    }

    if (!mainObject.contains("value")) {
        return parseError("Could not find the 'value' property for a forminput command.");
    }

    InjectionValue value;
    if (mainObject["value"].type() == QVariant::String) {
        value = InjectionValue(mainObject["value"].toString());
    } else if (mainObject["value"].type() == QVariant::Int
               || mainObject["value"].type() == QVariant::UInt
               || mainObject["value"].type() == QVariant::LongLong
               || mainObject["value"].type() == QVariant::ULongLong) {
        value = InjectionValue(mainObject["value"].toInt());
    } else if (mainObject["value"].type() == QVariant::Bool) {
        value = InjectionValue(mainObject["value"].toBool());
    } else {
        return parseError("The 'value' property for a forminput command must be a string, int or bool.");
    }

    // There may be an optional 'method' entry.
    FormInputCommand::InputSimulationMethod method = FormInputCommand::OnChange; // By default use onchange-triggerng.
    QString methodRequested = "onchange";
    if (mainObject.contains("method")) {
        if (mainObject["method"].type() != QVariant::String) {
            return parseError("The 'method' property for a forminput command must be a string.");
        }

        methodRequested = mainObject["method"].toString();
        if (methodRequested == "inject") {
            method = FormInputCommand::Inject;
        } else if (methodRequested == "onchange") {
            method = FormInputCommand::OnChange;
        } else if (methodRequested == "simulate-js") {
            method = FormInputCommand::SimulateJS;
        } else if (methodRequested == "simulate-gui") {
            method = FormInputCommand::SimulateGUI;
        } else {
            return parseError("The 'method' property for a forminput command must be one of 'inject', 'onchange', 'simulate-js' or 'simulate-gui'.");
        }
    }

    // There may be an optional 'noblur' entry.
    bool noBlur = false; // default to triggering the 'blur' event.
    if (mainObject.contains("noblur")) {
        if (mainObject["noblur"].type() != QVariant::Bool) {
            return parseError("The 'noblur' property for a forminput command must be a boolean.");
        }

        noBlur = mainObject["noblur"].toBool();
    }

    return FormInputCommandPtr(new FormInputCommand(mainObject["field"].toString(), value, method, methodRequested, noBlur));
}

CommandPtr RequestHandler::xpathCommand(QVariantMap mainObject)
{
    Log::debug("  Request handler: Building xpath evaluation command.");

    // Fetch the XPath
    if (!mainObject.contains("xpath")) {
        return parseError("Could not find the 'xpath' property for an xpath command.");
    }

    QStringList xPaths;
    bool singleton;

    if (mainObject["xpath"].type() == QVariant::String) {
        singleton = true;
        xPaths.append(mainObject["xpath"].toString());

    } else if (mainObject["xpath"].type() == QVariant::List) {
        singleton = false;
        foreach (QVariant entry, mainObject["xpath"].toList()) {
            if (entry.type() == QVariant::String) {
                xPaths.append(entry.toString());
            } else {
                return parseError("The 'xpath' property for an xpath command must be a string or list of strings.");
            }
        }

    } else {
        return parseError("The 'xpath' property for an xpath command must be a string or list of strings.");
    }

    return XPathCommandPtr(new XPathCommand(xPaths, singleton));
}

CommandPtr RequestHandler::eventCommand(QVariantMap mainObject)
{
    Log::debug("  Request handler: Building event-trigger command.");

    // Fetch the XPath
    if (!mainObject.contains("element")) {
        return parseError("Could not find the 'element' property for an event command.");
    }

    if (mainObject["element"].type() != QVariant::String) {
        return parseError("The 'element' property for an event command must be a string.");
    }

    // Fetch the event name
    if (!mainObject.contains("event")) {
        return parseError("Could not find the 'event' property for an event command.");
    }

    if (mainObject["event"].type() != QVariant::String) {
        return parseError("The 'event' property for an event command must be a string.");
    }

    return EventTriggerCommandPtr(new EventTriggerCommand(mainObject["element"].toString(), mainObject["event"].toString()));
}

CommandPtr RequestHandler::windowsizeCommand(QVariantMap mainObject)
{
    Log::debug("  Request handler: Building window-size command.");

    int width, height;
    bool ok;

    if (!mainObject.contains("width")) {
        return parseError("Could not find the 'width' property for a windowsize command.");
    }

    width = mainObject["width"].toInt(&ok);
    if (!ok) {
        return parseError("The 'width' property for a windowsize command must be an integer.");
    }

    if (!mainObject.contains("height")) {
        return parseError("Could not find the 'height' property for a windowsize command.");
    }

    height = mainObject["height"].toInt(&ok);
    if (!ok) {
        return parseError("The 'height' property for a windowsize command must be an integer.");
    }

    if (width < 0 || width > 3000) {
        return parseError("The 'width' property for a windowsize command must be between 0 and 3000.");
    }

    if (height < 0 || height > 3000) {
        return parseError("The 'height' property for a windowsize command must be between 0 and 3000.");
    }

    return WindowSizeCommandPtr(new WindowSizeCommand(width, height));
}

CommandPtr RequestHandler::concolicAdviceCommand(QVariantMap mainObject)
{
    Log::debug("  Request handler: Building concolic-advice command.");

    ConcolicAdviceCommand::ConcolicAdviceAction action;
    QString sequence;
    int amount = 1;

    if (!mainObject.contains("action")) {
        return parseError("Could not find the 'action' property for a conclicadvice command.");
    }

    if (mainObject["action"].type() != QVariant::String) {
        return parseError("The 'action' property for a concolicadvice command must be a string.");
    }

    QString actionString = mainObject["action"].toString();
    if (actionString == "begintrace") {
        action = ConcolicAdviceCommand::BeginTrace;
    } else if (actionString == "endtrace") {
        action = ConcolicAdviceCommand::EndTrace;
    } else if (actionString == "advice") {
        action = ConcolicAdviceCommand::Advice;
    } else {
        return parseError("The 'action' property for a concolicadvice command was not recognised.");
    }

    if (!mainObject.contains("sequence")) {
        return parseError("Could not find the 'sequence' property for a conclicadvice command.");
    }

    if (mainObject["sequence"].type() != QVariant::String) {
        return parseError("The 'sequence' property for a concolicadvice command must be a string.");
    }

    sequence = mainObject["sequence"].toString();

    if (sequence.isEmpty()) {
        return parseError("The 'sequence' property of a concolicadvice command should be non-empty.");
    }

    if (mainObject.contains("amount")) {
        bool ok;
        amount = mainObject["amount"].toUInt(&ok);

        if (!ok) {
            return parseError("The 'amount' property for a concolicadvice command must be a non-negative integer.");
        }
    }

    return ConcolicAdviceCommandPtr(new ConcolicAdviceCommand(action, sequence, amount));
}


}
