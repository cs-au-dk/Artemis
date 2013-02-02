/*
  Copyright 2011 Simon Holm Jensen. All rights reserved.

  Redistribution and use in source and binary forms, with or without modification, are
  permitted provided that the following conditions are met:

     1. Redistributions of source code must retain the above copyright notice, this list of
        conditions and the following disclaimer.

     2. Redistributions in binary form must reproduce the above copyright notice, this list
        of conditions and the following disclaimer in the documentation and/or other materials
        provided with the distribution.

  THIS SOFTWARE IS PROVIDED BY SIMON HOLM JENSEN ``AS IS'' AND ANY EXPRESS OR IMPLIED
  WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND
  FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL <COPYRIGHT HOLDER> OR
  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
  CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
  SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
  ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
  NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
  ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

  The views and conclusions contained in the software and documentation are those of the
  authors and should not be interpreted as representing official policies, either expressed
  or implied, of Simon Holm Jensen
*/

#include <assert.h>

#include "artemisglobals.h"

#include "formfield.h"

namespace artemis
{

/**
 * @brief Takes ownership of element
 * @param parent
 * @param type
 * @param element
 * @param input_options
 */
FormField::FormField(QObject* parent, FormFieldTypes type, DOMElementDescriptor* element, QSet<QString> input_options) : QObject(parent)
{
    this->field_type = type;

    this->element_descriptor = element;
    this->element_descriptor->setParent(this);

    this->inputs_set = input_options;
}

/**
 * @brief Takes ownership of element
 * @param parent
 * @param type
 * @param element
 */
FormField::FormField(QObject* parent, FormFieldTypes type, DOMElementDescriptor* element) : QObject(parent)
{
    this->field_type = type;

    this->element_descriptor = element;
    this->element_descriptor->setParent(this);
}

FormField::FormField(QObject* parent, const FormField* other) : QObject(parent)
{
    this->field_type = other->field_type;
    this->inputs_set = other->inputs_set;
    this->element_descriptor = new DOMElementDescriptor(parent, other->element_descriptor);
}

FormField::~FormField()
{

}

DOMElementDescriptor* FormField::element() const
{
    return element_descriptor;
}

FormFieldTypes FormField::type()
{
    return field_type;
}

QSet<QString> FormField::inputs()
{
    return inputs_set;
}

QDebug operator<<(QDebug dbg, const FormField& f)
{
    dbg.nospace() << "{" << *f.element_descriptor << "," << form_field_type_tostring(f.field_type) << "," << f.inputs_set << "}";
    return dbg.space();
}

FormFieldTypes get_type_from_attr(QString type_attr)
{
    if (type_attr.isEmpty())
        { return TEXT; } //de facto standard;

    type_attr = type_attr.toLower();
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

    if (type_attr == "button"
        || type_attr == "hidden"
        || type_attr == "submit"
        || type_attr == "reset"
        || type_attr == "image")
        { return NO_INPUT; }

    if (type_attr == "checkbox"
        || type_attr == "radio")
        { return BOOLEAN; }

    if (type_attr == "password"
        || type_attr == "text"
        || type_attr == "email"
        || type_attr == "file")
        { return TEXT; }

    qFatal("Unknown type attribute on form element: %s", type_attr.toStdString().c_str());
    assert(false);
}
}
