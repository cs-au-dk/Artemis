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

#include <assert.h>

#include <QWebElement>
#include <QWebElementCollection>
#include <QWebFrame>
#include <QHash>

#include "clicksimulator.h"

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

    // Look up the element and trigger the event

    QWebElement target = page->getSingleElementByXPath(mTargetXPath);
    if (target.isNull()) {
        Log::error("ClickInput: Tried to click target XPath which could not be identified.");
        return;
    }

    ClickSimulator::clickByGuiSimulation(target, page);
    return;
}

BaseInputConstPtr ClickInput::getPermutation(const FormInputGeneratorConstPtr &formInputGenerator, const EventParameterGeneratorConstPtr &eventParameterGenerator, const TargetGeneratorConstPtr &targetGenerator, const ExecutionResultConstPtr &result) const
{
    // No permutations, just return a new ClickInput with the same parameters (as in timerinput.cpp).
    return BaseInputConstPtr(NULL);
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
