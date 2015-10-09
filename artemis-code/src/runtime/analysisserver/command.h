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

#ifndef COMMAND_H
#define COMMAND_H

#include <QString>
#include <QUrl>
#include <QSharedPointer>
#include <QStringList>

#include "util/loggingutil.h"
#include "runtime/input/forms/injectionvalue.h"

namespace artemis
{

class AnalysisServerRuntime;

/**
 * These classes represent the types of command which can be sent to the analysis server.
 *
 * When the Runtime is given a Command to execute, it can use a polymorphic method to take action depending on
 * which conrete subclass it has been given.
 */

class Command
{
public:
    virtual void accept(AnalysisServerRuntime* server) = 0;
    virtual ~Command() {}
};

typedef QSharedPointer<Command> CommandPtr;
// Metatype declaration is at the bottom, outside the namespace.

// To end the server.
class ExitCommand : public Command
{
public:
    virtual void accept(AnalysisServerRuntime* server);
};

typedef QSharedPointer<ExitCommand> ExitCommandPtr;

// Some error ocurred in parsing the request.
class ErrorCommand : public Command
{
public:
    ErrorCommand(QString message)
        : message(message)
    {}
    virtual void accept(AnalysisServerRuntime* server);

    QString message;
};

typedef QSharedPointer<ErrorCommand> ErrorCommandPtr;

// Echo; used for testing
class EchoCommand : public Command
{
public:
    EchoCommand(QString message, uint delay)
        : message(message)
        , delay(delay)
    {}
    virtual void accept(AnalysisServerRuntime* server);

    QString message;
    uint delay;
};

typedef QSharedPointer<EchoCommand> EchoCommandPtr;

// Load a new page
class PageLoadCommand : public Command
{
public:
    PageLoadCommand(QUrl url, uint timeout)
        : url(url)
        , timeout(timeout)
    {}
    virtual void accept(AnalysisServerRuntime* server);

    QUrl url;
    uint timeout;
};

typedef QSharedPointer<PageLoadCommand> PageLoadCommandPtr;

// Gets a list of event handlers from the page.
class HandlersCommand : public Command
{
public:
    HandlersCommand(QString filter)
        : filter(filter)
    {}

    virtual void accept(AnalysisServerRuntime* server);

    QString filter; // May be null if no filter element has been given.
};

typedef QSharedPointer<HandlersCommand> HandlersCommandPtr;

// Clicks an element using an XPath locator.
// TODO: Add a choice of JS-level and GUI-level clicks. Onlty JS-level is implemented for now.
class ClickCommand : public Command
{
public:
    enum ClickSimulationMethod { Simple, SimulateJS, SimulateGUI };

    ClickCommand(QString xPath, ClickSimulationMethod method, QString methodStr)
        : xPath(xPath)
        , method(method)
        , methodStr(methodStr)
    {}
    virtual void accept(AnalysisServerRuntime* server);

    QString xPath;
    ClickSimulationMethod method;
    QString methodStr;
};

typedef QSharedPointer<ClickCommand> ClickCommandPtr;

// Gets information about the current page.
class PageStateCommand : public Command
{
public:
    PageStateCommand(bool includeDom)
        : includeDom(includeDom)
    {}
    virtual void accept(AnalysisServerRuntime* server);

    bool includeDom;
};

typedef QSharedPointer<PageStateCommand> PageStateCommandPtr;

// Gets information about a certain element.
class ElementCommand : public Command
{
public:
    ElementCommand(QString xPath, QString property)
        : xPath(xPath)
        , property(property)
    {}
    virtual void accept(AnalysisServerRuntime* server);

    QString xPath;
    QString property; // Null if no property was requested.
};

typedef QSharedPointer<ElementCommand> ElementCommandPtr;

// Lists the fields read by each event.
class FieldsReadCommand : public Command
{
public:
    virtual void accept(AnalysisServerRuntime* server);
};

typedef QSharedPointer<FieldsReadCommand> FieldsReadCommandPtr;

// Uses the browser history to go back one page.
class BackButtonCommand : public Command
{
public:
    virtual void accept(AnalysisServerRuntime* server);
};

typedef QSharedPointer<BackButtonCommand> BackButtonCommandPtr;

// Fills a form field with a given value.
class FormInputCommand : public Command
{
public:
    enum InputSimulationMethod { Inject, OnChange, SimulateJS, SimulateGUI };

    FormInputCommand(QString field, InjectionValue value, InputSimulationMethod method, QString methodStr, bool noBlur)
        : field(field)
        , value(value)
        , method(method)
        , methodStr(methodStr)
        , noBlur(noBlur)
    {}
    virtual void accept(AnalysisServerRuntime* server);

    QString field;
    InjectionValue value;
    InputSimulationMethod method;
    QString methodStr;
    bool noBlur;
};

typedef QSharedPointer<FormInputCommand> FormInputCommandPtr;

// Evaluates a list of XPath queries and returns the results.
class XPathCommand : public Command
{
public:
    XPathCommand(QStringList xPaths, bool formatSingleton)
        : xPaths(xPaths)
        , formatSingleton(formatSingleton)
    {}
    virtual void accept(AnalysisServerRuntime* server);

    QStringList xPaths;
    bool formatSingleton;
};

typedef QSharedPointer<XPathCommand> XPathCommandPtr;

// Triggers any event on an element.
class EventTriggerCommand : public Command
{
public:
    EventTriggerCommand(QString xPath, QString event)
        : xPath(xPath)
        , event(event)
    {}
    virtual void accept(AnalysisServerRuntime* server);

    QString xPath;
    QString event;
};

typedef QSharedPointer<EventTriggerCommand> EventTriggerCommandPtr;

// Resizes the browser window.
class WindowSizeCommand : public Command
{
public:
    WindowSizeCommand(int width, int height)
        : width(width)
        , height(height)
    {}
    virtual void accept(AnalysisServerRuntime* server);

    int width;
    int height;
};

typedef QSharedPointer<WindowSizeCommand> WindowSizeCommandPtr;

// Command to handle all aspects of recording concolic traces and giving concolic advice.
class ConcolicAdviceCommand : public Command
{
public:
    enum ConcolicAdviceAction { BeginTrace, EndTrace, Advice };

    ConcolicAdviceCommand(ConcolicAdviceAction action, QString sequence, uint amount)
        : action(action)
        , sequence(sequence)
        , amount(amount)
    {}
    virtual void accept(AnalysisServerRuntime* server);

    ConcolicAdviceAction action;
    QString sequence;
    uint amount;
};

typedef QSharedPointer<ConcolicAdviceCommand> ConcolicAdviceCommandPtr;




} // namespace artemis


Q_DECLARE_METATYPE(artemis::CommandPtr)
//qRegisterMetaType<artemis::CommandPtr>();


#endif // COMMAND_H
