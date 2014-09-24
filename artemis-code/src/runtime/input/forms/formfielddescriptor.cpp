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
#include <QDebug>

#include "artemisglobals.h"

#include "formfielddescriptor.h"

namespace artemis
{

FormFieldDescriptor::FormFieldDescriptor(FormFieldTypes type, DOMElementDescriptorConstPtr element, QSet<QString> inputOptions) :
    mFieldType(type),
    mDomElementDescriptor(element),
    mInputOptions(inputOptions)
{

}

FormFieldDescriptor::FormFieldDescriptor(FormFieldTypes type, DOMElementDescriptorConstPtr element) :
    mFieldType(type),
    mDomElementDescriptor(element)
{

}

QDebug operator<<(QDebug dbg, const FormFieldDescriptor& f)
{
    dbg.nospace() << "{" << f.mDomElementDescriptor->toString() << "," << f.formFieldTypeTostring(f.mFieldType) << "," << f.mInputOptions << "}";
    return dbg.space();
}

FormFieldTypes getTypeFromAttr(QString typeAttr)
{
    if (typeAttr.isEmpty()) {
        return TEXT;
    } //de facto standard;

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

    // Should match the list in CodeGeneratorJS.pm
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
        || typeAttr == "email" //HTML5
        || typeAttr == "file"
        || typeAttr == "search" //HTML5
        || typeAttr == "url" //HTML5
        || typeAttr == "week" //HTML5
        || typeAttr == "time" //HTML5
        || typeAttr == "tel" //HTML5
        || typeAttr == "range" //HTML5
        || typeAttr == "number" //HTML5
        || typeAttr == "month" //HTML5
        || typeAttr == "datetime-local" //HTML5
        || typeAttr == "datetime" //HTML5
        || typeAttr == "date" //HTML5
        || typeAttr == "color" //HTML5
            )
        { return TEXT; }

    qWarning() << "WARN: Unknown type attribute on form element: " << typeAttr;
    return TEXT;
}
}
