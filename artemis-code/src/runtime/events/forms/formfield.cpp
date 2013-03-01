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

#include <assert.h>

#include "artemisglobals.h"

#include "formfield.h"

namespace artemis
{

FormField::FormField(FormFieldTypes type, const DOMElementDescriptor* element, QSet<QString> inputOptions) :
    mElementDescriptor(element), mFieldType(type)
{
    this->mDefaultInputs = inputOptions;
}

FormField::FormField(FormFieldTypes type, const DOMElementDescriptor* element) :
    mElementDescriptor(element), mFieldType(type)
{

}

const DOMElementDescriptor* FormField::getDomElement() const
{
    return mElementDescriptor;
}

FormFieldTypes FormField::getType() const
{
    return mFieldType;
}

QSet<QString> FormField::getInputOptions() const
{
    return mDefaultInputs;
}

QDebug operator<<(QDebug dbg, const FormField& f)
{
    dbg.nospace() << "{" << *f.mElementDescriptor << "," << formFieldTypeTostring(f.mFieldType) << "," << f.mDefaultInputs << "}";
    return dbg.space();
}

FormFieldTypes getTypeFromAttr(QString typeAttr)
{
    if (typeAttr.isEmpty())
        { return TEXT; } //de facto standard;

    typeAttr = typeAttr.toLower();
    /** Types :
        button
        checkbox
        file
        hidden
        image
        password
        radio
        reset
        submit
        text
    */

    if (typeAttr == "button"
        || typeAttr == "hidden"
        || typeAttr == "submit"
        || typeAttr == "reset"
        || typeAttr == "image")
        { return NO_INPUT; }

    if (typeAttr == "checkbox"
        || typeAttr == "radio")
        { return BOOLEAN; }

    if (typeAttr == "password"
        || typeAttr == "text"
        || typeAttr == "textbox" //YAHOO FIX
        || typeAttr == "email"
        || typeAttr == "file")
        { return TEXT; }

    qDebug() << "Unknown type attribute on form element: %s"<< typeAttr;
    assert(false);
}
}
