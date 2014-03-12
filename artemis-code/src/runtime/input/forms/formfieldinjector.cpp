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
    if (element.isNull()) {
        qDebug() << "Warning: failed to inject input.\n";
        statistics()->accumulate("Concolic::FailedInjections", 1); // TODO: this is called even in non-concolic modes!
        return false;
    }

    if (element.attribute("type", "") == "checkbox" || element.attribute("type", "") == "radio") {

        // We only expect to inject bool values into checkboxes or radio buttons. Reject string values.
        if (value.isString()) {
            qDebug() << "Warning: failed to inject input " << element.toPlainText() << ": expected a BOOL.\n";
            statistics()->accumulate("Concolic::FailedInjections", 1); // TODO: this is called even in non-concolic modes!
            return false;
        }

        // Setting the checked property via JavaScript injection allows WebKit to correctly update the state of the
        // page, for example by unsetting other inputs in the same radio button group.
        if (value.getBool()) {
            element.evaluateJavaScript("this.checked = true;");
        } else {
            element.evaluateJavaScript("this.checked = false;");
        }

    } else {
        // For all other input types we expect a string injection.
        if (!value.isString()) {
            qDebug() << "Warning: failed to inject input " << element.toPlainText() << ": expected a STRING.\n";
            statistics()->accumulate("Concolic::FailedInjections", 1); // TODO: this is called even in non-concolic modes!
            return false;
        }

        // We do this using JavaScript because some values are only correctly set this way
        // E.g. if you set the value of a select box then this approach correctly updates the node,
        // where the setAttribute approach updates the value itself but not the remaining state of the node

        // TODO this is a bit risky, what if this triggers other events?

        QString setValue = QString("this.value = \"") + value.getString() + "\";";
        element.evaluateJavaScript(setValue);

    }
    // TODO: Do we need any other cases here?
    // For example seperate handling of "select" types where we could inject by index?

    return true;
}


} // namespace artemis
