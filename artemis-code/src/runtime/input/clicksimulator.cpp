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

#include "clicksimulator.h"

#include <QWebFrame>
#include <QMouseEvent>
#include <QApplication>

#include "util/loggingutil.h"
#include "forms/formfieldinjector.h"

namespace artemis
{

void ClickSimulator::clickByEvent(QWebElement element)
{
    if (element.isNull()) {
        return;
    }

    // Do not hide this click from Artemis' instrumentation.
    element.evaluateJavaScript("this.click()", QUrl(), false);
}

/**
 * Uses a sequence of JavaScript events to simulate a user clicking a certain element.
 */
void ClickSimulator::clickByUserEventSimulation(QWebElement element)
{
    if (element.isNull()) {
        return;
    }

    triggerHandler(element, "mouseover");
    triggerHandler(element, "mousemove");
    triggerHandler(element, "mousedown");
    triggerHandler(element, "focus");
    triggerHandler(element, "mouseup");
    triggerHandler(element, "click");
    triggerHandler(element, "mousemove");
    triggerHandler(element, "mouseout");
    triggerHandler(element, "blur"); // TODO: Might need a 'noblur' option?
}

void ClickSimulator::triggerHandler(QWebElement element, QString eventName)
{
    // TODO: This general method doesn't really belong in FormFieldInjector at all...
    FormFieldInjector::triggerHandler(element, eventName);
}

/**
 * Simulates a GUI-level click on an element.
 *
 * Method:
 *      Find coordinates of the centre of the element.
 *      Scroll viewport to show element.
 *      Generate a GUI click at those coordinates.
 */
void ClickSimulator::clickByGuiSimulation(QWebElement element, ArtemisWebPagePtr page)
{
    QPoint targetCoords = getElementCoordinatesInViewport(element, page);
    QSize viewportSize = page->viewportSize();

    Log::debug(QString("ClickSimulator: Clicking on viewport coordinates (%1, %2)").arg(targetCoords.x()).arg(targetCoords.y()).toStdString());
    Log::debug(element.toOuterXml().toStdString());
    Log::debug((QString("Dimensions of web view are X: ") + QString::number(viewportSize.width()) + " Y: " + QString::number(viewportSize.height()) + " Scrollbar position is X: " + QString::number(page->mainFrame()->scrollBarValue(Qt::Horizontal)) + " Y:" + QString::number(page->mainFrame()->scrollBarValue(Qt::Vertical))).toStdString());

    if ((viewportSize.width() + page->mainFrame()->scrollBarValue(Qt::Horizontal)) < targetCoords.x() ||
        (viewportSize.height() + page->mainFrame()->scrollBarValue(Qt::Vertical)) < targetCoords.y()) {

        Log::debug("Target outside viewport, repositioning");

        int xScroll = std::min(
            page->mainFrame()->contentsSize().width() - viewportSize.width(), // scroll to the far left
            std::max(
                0, // don't scroll
                targetCoords.x() - (viewportSize.width() / 2)
            )
        );

        page->mainFrame()->setScrollBarValue(Qt::Horizontal, xScroll);

        int yScroll = std::min(
            page->mainFrame()->contentsSize().height() - viewportSize.height(), // scroll to the bottom
            std::max(
                0, // don't scroll
                targetCoords.y() - (viewportSize.height() / 2)
            )
        );

        page->mainFrame()->setScrollBarValue(Qt::Vertical, yScroll);

        targetCoords = QPoint(targetCoords.x() - xScroll, targetCoords.y() - yScroll);

        Log::debug(QString("ClickSimulator: Changed coordinates to (%1, %2)").arg(targetCoords.x()).arg(targetCoords.y()).toStdString());

    }

    //element.setFocus(); // This is already implied by the browser handling the click.

    // Click the target element's coordinates.

    QMouseEvent mouseButtonPress(QEvent::MouseButtonPress, targetCoords, Qt::LeftButton, Qt::LeftButton, Qt::NoModifier);
    QApplication::sendEvent(page.data(), &mouseButtonPress);
    //assert(mouseButtonPress.isAccepted());

    QMouseEvent mouseButtonRelease(QEvent::MouseButtonRelease, targetCoords, Qt::LeftButton, Qt::LeftButton, Qt::NoModifier);
    QApplication::sendEvent(page.data(), &mouseButtonRelease);
    //assert(mouseButtonRelease.isAccepted());

}

QPoint ClickSimulator::getElementCoordinatesInViewport(QWebElement element, ArtemisWebPagePtr page)
{
    QPoint documentCoordinates = getElementCoordinatesInDocument(element);

    return QPoint(documentCoordinates.x() - page->mainFrame()->scrollBarValue(Qt::Horizontal),
                  documentCoordinates.y() - page->mainFrame()->scrollBarValue(Qt::Vertical));
}

QPoint ClickSimulator::getElementCoordinatesInDocument(QWebElement element)
{
    // For some reason targetElement.geometry().center(); does not seem to update correctly if the button moves during
    // the injection, so we are forced to pull the position from JavaScript. See issue #110.
    // We also can't simply use getBoundingClientRect() as this is only relative to the viewport.
    QVariant clickPoint = element.evaluateJavaScript("function findPos(obj) { var l=t=0; do { l+=obj.offsetLeft; t+=obj.offsetTop; }while(obj=obj.offsetParent); return [l,t]; } bb=this.getBoundingClientRect(); width=bb.right-bb.left; height=bb.bottom-bb.top; absPos=findPos(this); clickX=absPos[0] + width/2; clickY = absPos[1] + height/2; [Math.floor(clickX), Math.floor(clickY)];");
    return QPoint(clickPoint.toList()[0].toInt(), clickPoint.toList()[1].toInt());
}




} // namespace artemis
