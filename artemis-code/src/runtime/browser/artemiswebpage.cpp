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
#include <QWebFrame>

#include "artemisglobals.h"
#include "statistics/statsstorage.h"

#include "artemiswebpage.h"

namespace artemis
{

ArtemisWebPage::ArtemisWebPage() :
    QWebPage(NULL),
    mAcceptNavigation(true) // Unless we are in manual mode and choose otherwise, we accept all navigation.
{
}

void ArtemisWebPage::updateFormIdentifiers()
{
    QString js = "for (var i = 0; i < document.forms.length; i++) { var form = document.forms[i]; for (var j = 0; j < form.elements.length; j++) { form.elements[j].__ARTEMIS__FORM__IDENTIFIER__ = i + \"-\" + j; }}";
    currentFrame()->evaluateJavaScript(js);
}

void ArtemisWebPage::javaScriptAlert(QWebFrame* frame, const QString& msg)
{
    statistics()->accumulate("WebKit::alerts", 1);
    qDebug() << "JAVASCRIPT ALERT: " << msg;
    emit sigJavascriptAlert(frame, msg);
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


// This function is called whenever WebKit requests to navigate frame to the resource specified by request by means of the specified navigation type type.
bool ArtemisWebPage::acceptNavigationRequest(QWebFrame *frame, const QNetworkRequest &request, QWebPage::NavigationType type)
{
    // In demo mode it is useful to be able to intercept all page loads (so they can be passed through webkit executor).
    // By returning false here we forbid any within-page (i.e. via links, buttons, etc) navigation.
    // The request is passed via this signal to the demo mode and can be handled there.

    //qDebug() << "NAVIGATION: " << request.url().toString() << " Type: " << type;

    if (mAcceptNavigation || type == NavigationTypeOther) {
        // Allow NavigationTypeOther requests to pass through. It seems that these are really non-navigational XMLHttpRequests
        return true;

    } else {
        emit sigNavigationRequest(frame, request, type);
        return false;

        // NOTE: I thought there may be a problem here because this function cannot return until the signal has been
        // dealt with (which may result in a new page load itself).
        // However, it actually seems to be working correctly, so it looks like QWebView is able to handle these
        // overlapping loads cleanly after all.
    }
}

}
