/*
 * Copyright 2012 Aarhus University
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include "forminput.h"

#include "artemisglobals.h"

namespace artemis
{

FormInput::FormInput(QSet<QPair<QSharedPointer<const FormField>, const FormFieldValue*> >& inputs) :
    mInputs(inputs)
{
}

QSet<QSharedPointer<const FormField> > FormInput::getFields() const
{
    QSet<QSharedPointer<const FormField> > fields;

    foreach(input_t input, mInputs) {
        fields.insert(input.first);
    }

    return fields;
}

QSet<QPair<QSharedPointer<const FormField>, const FormFieldValue*> > FormInput::getInputs() const
{
    return mInputs;
}

void FormInput::writeToPage(ArtemisWebPagePtr page) const
{
    foreach(input_t input, mInputs) {

        const DOMElementDescriptor* elmDesc = input.first->getDomElement();
        QWebElement element = elmDesc->getElement(page);

        if (!element.isNull()) {
            element.setAttribute("value", input.second->stringRepresentation());
        }
    }
}

QDebug operator<<(QDebug dbg, FormInput* f)
{
    dbg.nospace() << f->mInputs;
    return dbg.space();
}

}


