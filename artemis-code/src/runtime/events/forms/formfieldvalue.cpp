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
#include "formfieldvalue.h"
#include <QDebug>
#include "artemisglobals.h"

namespace artemis
{

FormFieldValue::FormFieldValue(QObject* parent, QString value) : QObject(parent)
{
    this->str_val = value;
    is_bool = false;
    is_no_val = false;
}

FormFieldValue::FormFieldValue(QObject* parent, bool value) : QObject(parent)
{
    this->bool_val = value;
    is_bool = true;
    is_no_val = false;
}

FormFieldValue::FormFieldValue(QObject* parent) : QObject(parent)
{
    is_bool = false;
    is_no_val = true;
}

bool FormFieldValue::get_bool()
{
    Q_ASSERT(is_bool);
    Q_ASSERT(!is_no_val);
    return bool_val;
}

QString FormFieldValue::get_str()
{
    Q_ASSERT(!is_bool);
    Q_ASSERT(!is_no_val);
    return str_val;
}

bool FormFieldValue::is_no_value()
{
    return is_no_val;
}

QString FormFieldValue::string_representation()
{
    Q_ASSERT(!is_no_val);

    if (is_bool)
        { return bool_tostring(bool_val); }

    return str_val;
}

QDebug operator<<(QDebug dbg, const FormFieldValue& f)
{
    if (f.is_bool)
        { dbg.nospace() << f.bool_val; }
    else if (!f.is_no_val)
        { dbg.nospace() << f.str_val; }
    else
        { dbg.nospace() << "<no value>"; }

    return dbg.space();
}
}
