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

#include <QApplication>
#include <QMouseEvent>
#include <QWebElement>
#include <QWebElementCollection>
#include <QWebFrame>
#include <QHash>

#include "clickinput.h"

namespace artemis {

ClickInput::ClickInput(QString targetXPath, FormInputCollectionConstPtr formInput) :
    mTargetXPath(targetXPath),
    mFormInput(formInput)
{
}

void ClickInput::apply(ArtemisWebPagePtr page, QWebExecutionListener *webkitListener) const
{
    // Prepare forms

    mFormInput->writeToPage(page);

    // Trigger event

    // TODO: This code is duplicated in DemoModeMainWindow.

    // Find the element on the page (by injecting JS to do the XPath lookup)

    QWebElement document = page->currentFrame()->documentElement();
    QString escapedXPath(mTargetXPath);
    escapedXPath.replace('"', "\\\"");
    QString jsInjection = QString("var ArtFormButtons = document.evaluate(\"%1\", document, null, XPathResult.UNORDERED_NODE_SNAPSHOT_TYPE, null); for(var i = 0; i < ArtFormButtons.snapshotLength; i++){ ArtFormButtons.snapshotItem(i).setAttribute('artformbutton', 'true'); };").arg(escapedXPath);
    document.evaluateJavaScript(jsInjection, QUrl(), true);
    // TODO: look into whether we could read any useful results from this call.

    QWebElementCollection matches = document.findAll("*[artformbutton]");

    // Check that the result exists and is unique.
    if(matches.count() != 1){
        Log::error(QString("Error: The manual entry point XPath specified found %1 elements; there should be exactly 1.").arg(matches.count()).toStdString());
        exit(1);
    }
    QWebElement targetElement = matches.at(0);

    // Find the coordinates of the element
    QPoint targetCoords = targetElement.geometry().center();

    Log::debug(QString("ClickInput: Clicking on coordinates (%1, %2) for XPath query \"%3\"").arg(targetCoords.x()).arg(targetCoords.y()).arg(mTargetXPath).toStdString());
    Log::debug(targetElement.toOuterXml().toStdString());


    // Click the target element's coordinates.

    QMouseEvent mouseButtonPress(QEvent::MouseButtonPress, targetCoords, Qt::LeftButton, Qt::LeftButton, Qt::NoModifier);
    QApplication::sendEvent(page.data(), &mouseButtonPress);

    QMouseEvent mouseButtonRelease(QEvent::MouseButtonRelease, targetCoords, Qt::LeftButton, Qt::LeftButton, Qt::NoModifier);
    QApplication::sendEvent(page.data(), &mouseButtonRelease);

}

BaseInputConstPtr ClickInput::getPermutation(const FormInputGeneratorConstPtr &formInputGenerator, const EventParameterGeneratorConstPtr &eventParameterGenerator, const TargetGeneratorConstPtr &targetGenerator, const ExecutionResultConstPtr &result) const
{
    // No permutations, just return a new ClickInput with the same parameters (as in timerinput.cpp).
    return QSharedPointer<const BaseInput>(new ClickInput(mTargetXPath, mFormInput));
}

int ClickInput::hashCode() const
{
    return qHash(mTargetXPath);
}

QString ClickInput::toString() const
{
    return QString("ClickInput(%1)").arg(mTargetXPath);
}




} // namespace artemis
