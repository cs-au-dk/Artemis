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

#ifndef ANALYSISSERVERRUNTIME_H
#define ANALYSISSERVERRUNTIME_H

#include <QObject>

#include "runtime/runtime.h"
#include "runtime/analysisserver/analysisserver.h"

namespace artemis
{


class AnalysisServerRuntime : public Runtime
{
    Q_OBJECT

public:
    AnalysisServerRuntime(QObject* parent, const Options& options, const QUrl& url);

    void run(const QUrl& url);

    // Different methods to execute the different types of command.
    void execute(Command* command);
    void execute(ExitCommand* command);
    void execute(ErrorCommand* command);
    void execute(EchoCommand* command);
    void execute(PageLoadCommand* command);

protected:
    AnalysisServer mAnalysisServer;

    QVariant errorResponse(QString message);

protected slots:
    void slExecuteCommand(CommandPtr command);

signals:
    void sigCommandFinished(QVariant response);

};


} //namespace artemis
#endif // ANALYSISSERVERRUNTIME_H
