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

#include "util/loggingutil.h"

namespace artemis
{


/**
 * These structs represent the types of command which can be sent to the analysis server.
 *
 * When the Runtime is given a Command* to execute, it can use a polymorphic method to take action depending on
 * which conrete subclass it has been given.
 */

// Base class should not be instantiated.
struct Command
{
protected:
    Command() {}
};

// To end the server.
struct ExitCommand : public Command
{
};

// Echo; used for testing
struct EchoCommand : public Command
{
    EchoCommand(QString message)
        : message(message)
    {}

    QString message;
};

// Load a new page
struct PageLoadCommand : public Command
{
    PageLoadCommand(QUrl url)
        : url(url)
    {}

    QUrl url;
};


} // namespace artemis
#endif // COMMAND_H
