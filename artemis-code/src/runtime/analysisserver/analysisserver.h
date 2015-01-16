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

#ifndef ANALYSISSERVER_H
#define ANALYSISSERVER_H

#include <QAtomicInt>

#include <qhttpserverfwd.h>
#include <qjson/parser.h>

#include "command.h"

namespace artemis
{

class AnalysisServer : public QObject
{
    Q_OBJECT

public:
    AnalysisServer(quint16 port);

    ~AnalysisServer();

protected:
    QHttpServer* mServer;

    QAtomicInt mBusy;
    void rejectWhenBusy(QHttpRequest* request, QHttpResponse* response);

    QHttpResponse* waitingResponse;

private slots:
    void slHandleRequest(QHttpRequest* request, QHttpResponse* response);
    void slNewCommand(CommandPtr command);
    void slCommandFinished(QVariant response);
    void slResponseFinished();

signals:
    void sigExecuteCommand(CommandPtr command);
    void sigResponseFinished();
};

}


#endif // ANALYSISSERVER_H
