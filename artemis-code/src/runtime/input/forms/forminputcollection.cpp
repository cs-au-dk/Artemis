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
    mInputs(inputs),
    mTriggerOnAllFields(false)
{
}

FormInputCollection::FormInputCollection(const QList<FormInputPair> &inputs, bool triggerOnAllFields, QList<FormFieldDescriptorConstPtr> allFields) :
    mInputs(inputs),
    mTriggerOnAllFields(triggerOnAllFields),
    mAllFields(allFields)
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
    if(mTriggerOnAllFields) {
        // Loop over mAllFields and inject if we have a suitable value.
        // Note that this may inject less than the code below if mAllFields is not a superset of the fields in mInputs.
        foreach(FormFieldDescriptorConstPtr field, mAllFields) {
            foreach(FormInputPair input, mInputs) {
                if(input.first == field) {
                    QWebElement element = input.first->getDomElement()->getElement(page);
                    FormFieldInjector::inject(element, input.second);
                }
            }

            // do this not only for the form fields we inject into, but all of them
            field->getDomElement()->getElement(page).evaluateJavaScript(QString("this.symbolictrigger == \"\";"));
            field->getDomElement()->getElement(page).evaluateJavaScript(QString("this.options.symbolictrigger == \"\";"));

            emit sigInjectedToField(field);
        }

    } else {
        // Ignore mAllFields and just inject the values we know about.
        foreach(FormInputPair input, mInputs) {
            QWebElement element = input.first->getDomElement()->getElement(page);
            FormFieldInjector::inject(element, input.second);
            emit sigInjectedToField(input.first);
        }
    }

    emit sigFinishedWriteToPage();
}

QDebug operator<<(QDebug dbg, FormInputCollection* f)
{
    dbg.nospace() << f->mInputs;
    return dbg.space();
}

}


