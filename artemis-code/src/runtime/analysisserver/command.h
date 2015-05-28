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

#include "util/loggingutil.h"

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
    virtual void accept(AnalysisServerRuntime* server);
};

typedef QSharedPointer<HandlersCommand> HandlersCommandPtr;

// Clicks an element using an XPath locator.
// TODO: Add a choice of JS-level and GUI-level clicks. Onlty JS-level is implemented for now.
class ClickCommand : public Command
{
public:
    ClickCommand(QString xPath)
        : xPath(xPath)
    {}
    virtual void accept(AnalysisServerRuntime* server);

    QString xPath;
};

typedef QSharedPointer<ClickCommand> ClickCommandPtr;

// Gets information about the current page.
class DomCommand : public Command
{
public:
    virtual void accept(AnalysisServerRuntime* server);
};

typedef QSharedPointer<DomCommand> DomCommandPtr;

// Gets information about a certain element.
class ElementCommand : public Command
{
public:
    ElementCommand(QString xPath)
        : xPath(xPath)
    {}
    virtual void accept(AnalysisServerRuntime* server);

    QString xPath;
};

typedef QSharedPointer<ElementCommand> ElementCommandPtr;

// Lists the fields read by each event.
class FieldsReadCommand : public Command
{
public:
    virtual void accept(AnalysisServerRuntime* server);
};

typedef QSharedPointer<FieldsReadCommand> FieldsReadCommandPtr;







} // namespace artemis


Q_DECLARE_METATYPE(artemis::CommandPtr)
//qRegisterMetaType<artemis::CommandPtr>();


#endif // COMMAND_H
