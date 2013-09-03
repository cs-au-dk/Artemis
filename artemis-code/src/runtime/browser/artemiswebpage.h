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
#include <QNetworkRequest>

namespace artemis
{

class ArtemisWebPage : public QWebPage
{
    Q_OBJECT

public:
    explicit ArtemisWebPage();

    /**
     * Updates all form elements accessible through document.forms with a form identifier.
     *
     * The identifier is the form and element indexes written to the __ARTEMIS__FORM__IDENTIFIER__
     * property on the element. This is an alternative identification to the name and id
     * properties if they are not present.
     *
     * This is used primarily by the symbolic infrastructure to associate form inputs accross
     * exectutions. However, note that this approach is not robust if additional form elements
     * (or forms) are prepended to existing form elements (or forms), since this will change the
     * indexes.
     */
    void updateFormIdentifiers();

    void javaScriptAlert(QWebFrame* frame, const QString& msg);
    bool javaScriptConfirm(QWebFrame* frame, const QString& msg);
    void javaScriptConsoleMessage(const QString& message, int lineNumber, const QString& sourceID);
    bool javaScriptPrompt(QWebFrame* frame, const QString& msg, const QString& defaultValue, QString* result);

    bool mAcceptNavigation; // Used when in manual mode; see acceptNavigationRequest.

protected:
    virtual bool acceptNavigationRequest(QWebFrame *frame, const QNetworkRequest &request, NavigationType type);

signals:
    void sigJavascriptAlert(QWebFrame* frame, QString msg);
    void sigNavigationRequest(QWebFrame *frame, const QNetworkRequest &request, QWebPage::NavigationType type);
};

typedef QSharedPointer<ArtemisWebPage> ArtemisWebPagePtr;
typedef QSharedPointer<const ArtemisWebPage> ArtemisWebPageConstPtr;

}
#endif // ARTEMISWEBPAGE_H
