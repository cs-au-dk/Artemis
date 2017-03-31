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

#include "runtime/toplevel/analysisserverruntime.h"

namespace artemis
{

void ExitCommand::accept(AnalysisServerRuntime* server)
{
    server->execute(this);
}

void ErrorCommand::accept(AnalysisServerRuntime *server)
{
    server->execute(this);
}

void EchoCommand::accept(artemis::AnalysisServerRuntime *server)
{
    server->execute(this);
}

void PageLoadCommand::accept(AnalysisServerRuntime *server)
{
    server->execute(this);
}

void HandlersCommand::accept(AnalysisServerRuntime *server)
{
    server->execute(this);
}

void ClickCommand::accept(AnalysisServerRuntime *server)
{
    server->execute(this);
}

void PageStateCommand::accept(AnalysisServerRuntime *server)
{
    server->execute(this);
}

void ElementCommand::accept(AnalysisServerRuntime *server)
{
    server->execute(this);
}

void FieldsReadCommand::accept(AnalysisServerRuntime *server)
{
    server->execute(this);
}

void BackButtonCommand::accept(AnalysisServerRuntime *server)
{
    server->execute(this);
}

void FormInputCommand::accept(AnalysisServerRuntime *server)
{
    server->execute(this);
}

void XPathCommand::accept(AnalysisServerRuntime *server)
{
    server->execute(this);
}

void EventTriggerCommand::accept(AnalysisServerRuntime *server)
{
    server->execute(this);
}

void WindowSizeCommand::accept(AnalysisServerRuntime *server)
{
    server->execute(this);
}

void ConcolicAdviceCommand::accept(AnalysisServerRuntime *server)
{
    server->execute(this);
}

void EvaluateJsCommand::accept(AnalysisServerRuntime *server)
{
    server->execute(this);
}



} // namespace artemis
