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
#include "forminput.h"
#include "artemisglobals.h"


namespace artemis {

    FormInput::FormInput()
    {
    }

    FormInput::FormInput(const FormInput &other) {
        this->fields_set.clear();
        this->fields_set += other.fields_set;
    }

    void FormInput::write_to_page(QWebPage* page) {
        foreach (FormField ff, fields_set) {
            Q_ASSERT(this->values.contains(ff));

            DOMElementDescriptor elm_desc = ff.element();
            FormFieldValue value = values[ff];
            QWebElement element = elm_desc.get_element(page);

            if (!element.isNull()) {
                element.setAttribute("value", value.string_representation());
            }
        }
    }

    QSet<FormField> FormInput::fields() const {
        return this->fields_set;
    }

    void FormInput::add_field(const FormField f,const FormFieldValue fv) {
        fields_set.insert(f);
        values.insert(f,fv);
    }

    bool FormInput::operator==(FormInput& other) const {
        return this->fields_set == other.fields_set && this->values == other.values;
    }

    QDebug operator<<(QDebug dbg, const FormInput &f) {
        dbg.nospace() << f.values;
        return dbg.space();
    }

    uint FormInput::hashcode() const {
        return qHash(this->fields_set);
    }

    FormInput &FormInput::operator=(const FormInput &other) {
        this->fields_set.clear();
        this->values.clear();
        this->fields_set += other.fields_set;
        this->values = other.values;
        return *this;
    }
}


