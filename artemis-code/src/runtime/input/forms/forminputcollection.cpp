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

#include "artemisglobals.h"

#include "forminputcollection.h"

namespace artemis
{

FormInputCollection::FormInputCollection(const QList<FormInputPair>& inputs) :
    mInputs(inputs)
{
}

QSet<FormFieldDescriptorConstPtr> FormInputCollection::getFields() const
{
    QSet<FormFieldDescriptorConstPtr> fields;

    foreach(FormInputPair input, mInputs) {
        fields.insert(input.first);
    }

    return fields;
}

void FormInputCollection::writeToPage(ArtemisWebPagePtr page) const
{
    foreach(FormInputPair input, mInputs) {
        QWebElement element = input.first->getDomElement()->getElement(page);;

        if (!element.isNull()) {

            if (element.attribute("type", "") == "checkbox" || element.attribute("type", "") == "radio") {
                // all empty and "false" values are translated into unchecked state
                if (input.second.compare("") == 0 || input.second.compare("false") == 0) {
                    element.evaluateJavaScript("this.checked = false;");
                    element.setAttribute("value", "");
                } else {
                    element.evaluateJavaScript("this.checked = true;");
                    element.setAttribute("value", input.second);
                }

            } else {

                // We do this using JavaScript because some values are only correctly set this way
                // E.g. if you set the value of a select box then this approach correctly updates the node,
                // where the setAttribute approach updates the value itself but not the remaining state of the node

                // TODO this is a bit risky, what if this triggers other events?

                QString setValue = QString("this.value = \"") + input.second + "\";";
                element.evaluateJavaScript(setValue);

                //element.setAttribute("value", input.second);

            }
        }


    }
}

QDebug operator<<(QDebug dbg, FormInputCollection* f)
{
    dbg.nospace() << f->mInputs;
    return dbg.space();
}

}


