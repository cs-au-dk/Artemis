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
            element.setAttribute("value", input.second);
        }
    }
}

QDebug operator<<(QDebug dbg, FormInputCollection* f)
{
    dbg.nospace() << f->mInputs;
    return dbg.space();
}

}


