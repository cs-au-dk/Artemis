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

#include "formfieldinjector.h"

#include <QDebug>
#include "statistics/statsstorage.h"

namespace artemis
{

bool FormFieldInjector::inject(QWebElement element, InjectionValue value)
{
    QString setValue;

    if (element.isNull()) {
        qDebug() << "Warning: failed to inject input. Targeting null element.\n";
        Statistics::statistics()->accumulate("Concolic::FailedInjections", 1); // TODO: this is called even in non-concolic modes!
        return false;
    }

    // Depending on the variable type, we will inject in different ways.
    switch (value.getType()) {

    case QVariant::String:
        // We do this using JavaScript because some values are only correctly set this way
        // E.g. if you set the value of a select box then this approach correctly updates the node,
        // where the setAttribute approach updates the value itself but not the remaining state of the node

        setValue = QString("this.value = \"") + value.getString() + "\";";
        element.evaluateJavaScript(setValue);

        break;

    case QVariant::Bool:
        // Bool injection is only supported into checkbox and radio button input types.
        if (element.attribute("type", "") == "checkbox" || element.attribute("type", "") == "radio") {

            // Setting the checked property via JavaScript injection allows WebKit to correctly update the state of the
            // page, for example by unsetting other inputs in the same radio button group.
            if (value.getBool()) {
                element.evaluateJavaScript("this.checked = true;");
            } else {
                element.evaluateJavaScript("this.checked = false;");
            }

        } else {
            qDebug() << "Warning: failed to inject BOOL into input " << element.tagName() << " input: id:" << element.attribute("id", "") << ", classes:" << element.classes().join(",") << ".\n";
            Statistics::statistics()->accumulate("Concolic::FailedInjections", 1); // TODO: this is called even in non-concolic modes!
            return false;
        }

        break;

    case QVariant::Int:
        // Int injection is only supported into select boxes as the selectedIndex.
        if (element.tagName().toLower() == "select") {

            element.evaluateJavaScript(QString("this.selectedIndex = %1;").arg(value.getInt()));

        } else {
            qDebug() << "Warning: failed to inject INT into " << element.tagName() << " input: id:" << element.attribute("id", "") << ", classes:" << element.classes().join(",") << ".\n";
            Statistics::statistics()->accumulate("Concolic::FailedInjections", 1); // TODO: this is called even in non-concolic modes!
            return false;
        }
        break;

    default:
        qDebug() << "Error: Tried to inject a variable with an unknown type.\n";
        Statistics::statistics()->accumulate("Concolic::FailedInjections", 1); // TODO: this is called even in non-concolic modes!
        return false;
    }

    element.evaluateJavaScript(QString("this.symbolictrigger == \"\";"));
    element.evaluateJavaScript(QString("this.options.symbolictrigger == \"\";"));

    return true;
}

bool FormFieldInjector::injectAndTriggerChangeHandler(QWebElement element, InjectionValue value)
{
    if (inject(element, value)) {
        triggerChangeHandler(element);
        return true;
    } else {
        return false;
    }
}

bool FormFieldInjector::injectWithEventSimulation(QWebElement element, InjectionValue value)
{
    return false; // TODO
}





void FormFieldInjector::triggerHandler(QWebElement element, QString eventname)
{
    // eventName should be "change", "focus", etc. not "onchange", "onfocus", ...

    if (element.isNull()) {
        qDebug() << "Warning: failed to trigger event handler.\n";
        return;
    }

    QString jsInjection = QString("event = document.createEvent('HTMLEvents'); event.initEvent('%1', false, true); this.dispatchEvent(event);").arg(eventname);
    element.evaluateJavaScript(jsInjection);
}

void FormFieldInjector::triggerChangeHandler(QWebElement element)
{
    triggerHandler(element, "change");
}


} // namespace artemis
