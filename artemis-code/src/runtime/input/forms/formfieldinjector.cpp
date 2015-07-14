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
#include "util/loggingutil.h"

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
    /**
     * Simulate a human filling the form field as follows:
     *
     * For text inputs:
     *  focus
     *  For each character:
     *      If capital:
     *          keydown (shift)
     *      keydown
     *      keypress
     *      input
     *      keyup
     *      If capital:
     *          keyup (shift)
     *  change
     *  blur
     *
     * For checkbox inputs:
     *  focus
     *  click
     *  change
     *  blur
     *
     * For radio button inputs:
     *  focus
     *  click
     *  change
     *  blur
     *
     * N.B. These all fire on the newly checked radio button. There is no "deselect" or any other event on the
     * previously selected button.
     *
     * For select box inputs:
     *  focus
     *  change
     *  blur
     *
     * N.B. These fire on the select element itself. There is no event fired on the selected (or deselected) option
     * element. This can happen when clicking with a mouse, but
     *
     */

    // Handle each case separately.
    // TODO: Similar code duplicated in analysisserverruntime.cpp.
    if (element.tagName().toLower() == "input") {
        // For input fields, the allowable value type depends on the inupt type.
        // "radio" and "checkbox" inputs must have bool values, and all other input types must use "string".
        QString inputType = element.attribute("type").toLower();
        if (inputType == "checkbox" || inputType == "radio") {
            if (value.getType() == QVariant::Bool) {
                return simulateBooleanFieldFilling(element, value);
            } else {
                Log::debug("Could not inject non-bool into boolean field.");
                return false;
            }
        } else {
            if (value.getType() == QVariant::String) {
                return simulateTextFieldFilling(element, value.getString());
            } else {
                Log::debug("Could not inject non-string into text field.");
                return false;
            }
        }
    } else if (element.tagName().toLower() == "select") {
        // For select boxes we support injection of string or int (as selectedIndex) but not bool.
        if (value.getType() == QVariant::String || value.getType() == QVariant::Int) {
            return simulateSelectBoxFilling(element, value);;
        } else {
            Log::debug("Could not inject non-string and non-int into a select box.");
            return false;
        }
    } else {
        Log::debug("Could not inject into non-input field. Only 'input' and 'select' elements are supported.");
        return false;
    }
}

bool FormFieldInjector::simulateTextFieldFilling(QWebElement element, QString value)
{
    // Define some event triggering 'skeletons' to be used later.


    // %1 is the event name (e.g. "keydown"), %2 is the char (e.g. "H"), %3 is the keyCode/charCode, %4 is whether shift is used (e.g. "true").
    QString keyboardEventJS = QString("var ArtemisKeyboardEvent = document.createEvent('Events');"
                                      "ArtemisKeyboardEvent.initEvent('%1', true, true);"
                                      "ArtemisKeyboardEvent.key = '%2';"
                                      "ArtemisKeyboardEvent.char = '%2';"
                                      "ArtemisKeyboardEvent.keyCode = %3;"
                                      "ArtemisKeyboardEvent.charCode = %3;"
                                      "ArtemisKeyboardEvent.which = %3;"
                                      "ArtemisKeyboardEvent.shiftKey = %4;"
                                      "this.dispatchEvent(ArtemisKeyboardEvent);");

    QString inputEventJS = QString("var ArtemisInputEvent = document.createEvent('InputEvent');"
                                   "ArtemisInputEvent.initEvent('input', true, false);"
                                   "this.dispatchEvent(ArtemisInputEvent);");

    // %1 is ther value to inject.
    QString injectionJS = QString("this.value = \"%1\";");

    // First clear the field's contents
    // TODO: Simulate this as well.
    element.evaluateJavaScript(injectionJS.arg(""));

    triggerHandler(element, "focus"); // TODO: These events do not have the appropriate parameters or even event types.

    // Type the input charachter-by-character:
    for (int i = 0; i < value.length(); i++) {
        bool isCap = value[i].isUpper();
        QString shiftKey = "false";
        if (isCap) {
            shiftKey = "true";
            // Send 'Shift' keydown event.
            element.evaluateJavaScript(keyboardEventJS.arg("keydown", "", "16", "false"));
        }

        QString charCode = QString::number(value[i].toAscii());

        // Send keydown event
        element.evaluateJavaScript(keyboardEventJS.arg("keydown", value.at(i), charCode, shiftKey));

        // Send keypress event
        qDebug() << keyboardEventJS.arg("keypress", value.at(i), charCode, shiftKey);
        element.evaluateJavaScript(keyboardEventJS.arg("keypress", value.at(i), charCode, shiftKey));

        // Inject the input
        element.evaluateJavaScript(injectionJS.arg(value.left(i+1)));

        // Send input event
        element.evaluateJavaScript(inputEventJS);

        // Send keyup event
        element.evaluateJavaScript(keyboardEventJS.arg("keyup", value.at(i), charCode, shiftKey));

        if (isCap) {
            // Send 'Shift' keyup event.
            element.evaluateJavaScript(keyboardEventJS.arg("keyup", "", "16", "false"));
        }
    }

    // TODO: These events do not have the appropriate parameters or even event types.
    triggerHandler(element, "change");
    triggerHandler(element, "blur");

    return true;
}

bool FormFieldInjector::simulateBooleanFieldFilling(QWebElement element, InjectionValue value)
{
    // TODO: These events do not have the appropriate parameters or even event types.

    triggerHandler(element, "focus");
    triggerHandler(element, "click");
    bool result = inject(element, value);
    triggerHandler(element, "change");
    triggerHandler(element, "blur");

    return result;
}

bool FormFieldInjector::simulateSelectBoxFilling(QWebElement element, InjectionValue value)
{
    // TODO: These events do not have the appropriate parameters or even event types.

    triggerHandler(element, "focus");
    bool result = inject(element, value);
    triggerHandler(element, "change");
    triggerHandler(element, "blur");

    return result;
}



void FormFieldInjector::triggerHandler(QWebElement element, QString eventName)
{
    // eventName should be "change", "focus", etc. not "onchange", "onfocus", ...

    if (element.isNull()) {
        qDebug() << "Warning: failed to trigger event handler.\n";
        return;
    }

    // TODO: Strictly we should create an appropriate event type as listed in:
    // https://developer.mozilla.org/en-US/docs/Web/Events
    // https://developer.mozilla.org/en-US/docs/Web/API/Document/createEvent#Notes
    // For now we use generic "Event".
    QString eventType = "Event";
    QString eventInitMethod = "initEvent";

    QString bubbles = "false";
    QString cancellable = "true";

    QString jsInjection = QString("var event = document.createEvent('%1'); event.%2('%3', %4, %5); this.dispatchEvent(event);").arg(eventType, eventInitMethod, eventName, bubbles, cancellable);
    element.evaluateJavaScript(jsInjection);
}


void FormFieldInjector::triggerChangeHandler(QWebElement element)
{
    triggerHandler(element, "change");
}





} // namespace artemis
