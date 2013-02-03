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
 * @param inputOptions
 */
FormField::FormField(QObject* parent, FormFieldTypes type, DOMElementDescriptor* element, QSet<QString> inputOptions) : QObject(parent)
{
    this->fieldType = type;

    this->elementDescriptor = element;
    this->elementDescriptor->setParent(this);

    this->inputsSet = inputOptions;
}

/**
 * @brief Takes ownership of element
 * @param parent
 * @param type
 * @param element
 */
FormField::FormField(QObject* parent, FormFieldTypes type, DOMElementDescriptor* element) : QObject(parent)
{
    this->fieldType = type;

    this->elementDescriptor = element;
    this->elementDescriptor->setParent(this);
}

FormField::FormField(QObject* parent, const FormField* other) : QObject(parent)
{
    this->fieldType = other->fieldType;
    this->inputsSet = other->inputsSet;
    this->elementDescriptor = new DOMElementDescriptor(parent, other->elementDescriptor);
}

FormField::~FormField()
{

}

DOMElementDescriptor* FormField::element() const
{
    return elementDescriptor;
}

FormFieldTypes FormField::type() const
{
    return fieldType;
}

QSet<QString> FormField::inputs() const
{
    return inputsSet;
}

QDebug operator<<(QDebug dbg, const FormField& f)
{
    dbg.nospace() << "{" << *f.elementDescriptor << "," << formFieldTypeTostring(f.fieldType) << "," << f.inputsSet << "}";
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
        || typeAttr == "email"
        || typeAttr == "file")
        { return TEXT; }

    qFatal("Unknown type attribute on form element: %s", typeAttr.toStdString().c_str());
    assert(false);
}
}
