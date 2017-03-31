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

#ifndef REQUESTHANDLER_H
#define REQUESTHANDLER_H

#include <QString>
#include <QVariant>

#include <qhttpserverfwd.h>
#include <qjson/parser.h>

#include "analysisserver.h"
#include "command.h"

namespace artemis
{

/**
 * RequestHandler waits for all the request data to arrive, and parses the JSON request into a Command object.
 * If there is already an error at this stage, it simply creates an ErrorCommand with an appropriate message.
 */

class RequestHandler : public QObject
{
    Q_OBJECT

public:
    RequestHandler(QHttpRequest* request, QHttpResponse* response, AnalysisServer* server);
    ~RequestHandler();

protected:
    QHttpRequest* mRequest;
    QHttpResponse* mResponse;

    QVariant parseBody(QByteArray body);
    CommandPtr createCommand(QVariant data);
    CommandPtr parseError(QString message);

    QStringList unexpectedFields(QStringList expected, QVariantMap mainObject);
    CommandPtr unexpectedFieldsError(QString command, QStringList unexpected);

    CommandPtr exitCommand(QVariantMap mainObject);
    CommandPtr echoCommand(QVariantMap mainObject);
    CommandPtr pageloadCommand(QVariantMap mainObject);
    CommandPtr handlersCommand(QVariantMap mainObject);
    CommandPtr clickCommand(QVariantMap mainObject);
    CommandPtr pageCommand(QVariantMap mainObject);
    CommandPtr elementCommand(QVariantMap mainObject);
    CommandPtr fieldsReadCommand(QVariantMap mainObject);
    CommandPtr backbuttonCommand(QVariantMap mainObject);
    CommandPtr forminputCommand(QVariantMap mainObject);
    CommandPtr xpathCommand(QVariantMap mainObject);
    CommandPtr eventCommand(QVariantMap mainObject);
    CommandPtr windowsizeCommand(QVariantMap mainObject);
    CommandPtr concolicAdviceCommand(QVariantMap mainObject);
    CommandPtr evaluateJsCommand(QVariantMap mainObject);

protected slots:
    void slRequestFullyLoaded();

signals:
    void sigNewCommand(CommandPtr command);
    void sigServerLog(QString data, bool direction);
};

} // namespace artemis
#endif // REQUESTHANDLER_H
