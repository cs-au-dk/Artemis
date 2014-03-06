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

namespace artemis
{


bool FormFieldInjector::inject(QWebElement element, InjectionValue value)
{
    if (element.isNull()) {
        return false;
    }

    // TODO: Currently we only inject strings, so convert the InjectionValue into a string.
    // This will be replaced by more sophisticated injection soon.
    QString stringValue;
    if (value.isString()) {
        stringValue = value.getString();
    } else {
        stringValue = value.getBool() ? "true" : "false";
    }

    if (element.attribute("type", "") == "checkbox" || element.attribute("type", "") == "radio") {
        // all empty and "false" values are translated into unchecked state
        if (stringValue.compare("") == 0 || stringValue.compare("false") == 0) {
            element.evaluateJavaScript("this.checked = false;");
            element.setAttribute("value", "");
        } else {
            element.evaluateJavaScript("this.checked = true;");
            element.setAttribute("value", stringValue);
        }

    } else {

        // We do this using JavaScript because some values are only correctly set this way
        // E.g. if you set the value of a select box then this approach correctly updates the node,
        // where the setAttribute approach updates the value itself but not the remaining state of the node

        // TODO this is a bit risky, what if this triggers other events?

        QString setValue = QString("this.value = \"") + stringValue + "\";";
        element.evaluateJavaScript(setValue);

        //element.setAttribute("value", value);

    }

    return true; // TODO: Once we have detection of different input types and specialised injection we will be able to have a useful return value.
}


} // namespace artemis
