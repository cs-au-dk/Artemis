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
#include <QDebug>

#include "artemisglobals.h"
#include "statistics/statsstorage.h"

#include "artemiswebpage.h"

namespace artemis
{

ArtemisWebPage::ArtemisWebPage() : QWebPage(NULL)
{
}

void ArtemisWebPage::javaScriptAlert(QWebFrame*, const QString& msg)
{
    statistics()->accumulate("WebKit::alerts", 1);
    qDebug() << "JAVASCRIPT ALERT: " << msg;
}

bool ArtemisWebPage::javaScriptConfirm(QWebFrame* frame, const QString& msg)
{
    qDebug() << "JAVASCRIPT CONFIRM: " << msg;
    return true;
}

void ArtemisWebPage::javaScriptConsoleMessage(const QString& message, int lineNumber, const QString& sourceID)
{
    qDebug() << "JAVASCRIPT CONSOLE MESSAGES: " << message << " At line: " << lineNumber;
}

bool ArtemisWebPage::javaScriptPrompt(QWebFrame* frame, const QString& msg, const QString& defaultValue, QString* result)
{
    qDebug() << "JAVASCRIPT PROMPT: " << msg;
    *result = "TODO: You ask artemis, artemis gives you good response";
    return true;
}

}
