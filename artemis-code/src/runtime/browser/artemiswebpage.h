/*
 * Copyright 2012 Aarhus University
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
#ifndef ARTEMISWEBPAGE_H
#define ARTEMISWEBPAGE_H

#include <QWebPage>
#include <QString>
#include <QSharedPointer>

namespace artemis
{

class ArtemisWebPage : public QWebPage
{
    Q_OBJECT

public:
    explicit ArtemisWebPage();
    void javaScriptAlert(QWebFrame* frame, const QString& msg);
    bool javaScriptConfirm(QWebFrame* frame, const QString& msg);
    void javaScriptConsoleMessage(const QString& message, int lineNumber, const QString& sourceID);
    bool javaScriptPrompt(QWebFrame* frame, const QString& msg, const QString& defaultValue, QString* result);

};

typedef QSharedPointer<ArtemisWebPage> ArtemisWebPagePtr;
typedef QSharedPointer<const ArtemisWebPage> ArtemisWebPageConstPtr;

}
#endif // ARTEMISWEBPAGE_H
