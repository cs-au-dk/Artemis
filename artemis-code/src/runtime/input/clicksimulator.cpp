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

void ClickSimulator::clickByUserEventSimulation(QWebElement element)
{
    if (element.isNull()) {
        return;
    }

    // TODO
}

void ClickSimulator::triggerHandler(QWebElement element, QString eventName)
{
    // TODO: This doesn't really belong in FormFieldInjector at all...
    FormFieldInjector::triggerHandler(element, eventName);
}



} // namespace artemis
