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

#include <QDebug>
#include <QWebFrame>

#include "artemisglobals.h"
#include "statistics/statsstorage.h"
#include "model/coverage/coveragelistener.h"

#include "artemiswebpage.h"

namespace artemis
{

ArtemisWebPage::ArtemisWebPage() :
    QWebPage(NULL)
{
}

void ArtemisWebPage::updateFormIdentifiers()
{
    QString js = "for (var i = 0; i < document.forms.length; i++) { var form = document.forms[i]; for (var j = 0; j < form.elements.length; j++) { var element = form.elements[j]; if (element.id == \"\" || element.id.indexOf(\"ARTEMISID\") != -1) {element.id = \"ARTEMISID-\" + i + \"-\" + j;} }}";
    currentFrame()->documentElement().evaluateJavaScript(js, DONT_MEASURE_COVERAGE, true);
}

void ArtemisWebPage::javaScriptAlert(QWebFrame* frame, const QString& msg)
{
    Statistics::statistics()->accumulate("WebKit::alerts", 1);
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

void ArtemisWebPage::setCustomUserAgent(QString ua)
{
    mCustomUserAgent = ua;
}


QString ArtemisWebPage::userAgentForUrl(const QUrl &url) const
{
    if(mCustomUserAgent.isEmpty()) {
        return QWebPage::userAgentForUrl(url);
    } else {
        return mCustomUserAgent;
    }
}

// Returns the element uniquely identified by the given XPath.
// If no element is found, or multiple are matched, then a null element is returned.
QWebElement ArtemisWebPage::getSingleElementByXPath(QString xPath)
{
    QWebElementCollection allMatches = getElementsByXPath(xPath);

    if (allMatches.count() != 1) {
        Log::debug(QString("getSingleElementByXPath: Found %1 elements, but the XPath should match exactly one.").arg(allMatches.count()).toStdString());
        return QWebElement();
    }

    return allMatches.at(0);
}

QWebElementCollection ArtemisWebPage::getElementsByXPath(QString xPath)
{
    // To use QXmlQuery for XPath lookups we would need to parse the DOM as XML, and it will typically be invalid.
    // Instead we will inject some JavaScript to do the XPath lookup and then look up those elements from here.

    QString escapedXPath(xPath);
    escapedXPath.replace('"', "\\\"");

    QWebElement document = this->currentFrame()->documentElement();
    QString jsInjection = QString("var ArtemisSearchElts = document.evaluate(\"%1\", document, null, XPathResult.UNORDERED_NODE_SNAPSHOT_TYPE, null);"
                                  "for (var i=0; i < ArtemisSearchElts.snapshotLength; i++) {"
                                  "    ArtemisSearchElts.snapshotItem(i).setAttribute('artemissearch', 'true');"
                                  "};"
                                  "ArtemisSearchElts.snapshotLength;").arg(escapedXPath);
    int eltCount = document.evaluateJavaScript(jsInjection, QUrl(), true).toInt();

    if (eltCount == 0) {
        Log::debug(QString("getElementsByXPath: Found %1 elements, but the XPath should match at least one.").arg(eltCount).toStdString());
        return QWebElementCollection();
    }

    QWebElementCollection searchedElts = document.findAll("*[artemissearch]");
    assert(searchedElts.count() == eltCount);

    // Remove the 'artemissearch' marker so we can re-use it and avoid polluting the DOM more than necessary.
    foreach (QWebElement elt, searchedElts) {
        elt.removeAttribute("artemissearch");
    }

    return searchedElts;
}


// This function is called whenever WebKit requests to navigate frame to the resource specified by request by means of the specified navigation type type.
bool ArtemisWebPage::acceptNavigationRequest(QWebFrame *frame, const QNetworkRequest &request, QWebPage::NavigationType type)
{
    //qDebug() << "NAVIGATION: " << request.url().toString() << " Type: " << type;

    // Allow NavigationTypeOther requests to pass through. It seems that these are really non-navigational XMLHttpRequests
    if (type != NavigationTypeOther) {
        emit sigNavigationRequest(frame, request, type);
    }

    return true;
}

}
