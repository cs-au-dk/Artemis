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

#include <QDebug>

#include "artemisglobals.h"

#include "formfieldvalue.h"

namespace artemis
{

FormFieldValue::FormFieldValue(QObject* parent, QString value) : QObject(parent)
{
    strVal = value;
    isBool = false;
    isNoVal = false;
}

FormFieldValue::FormFieldValue(QObject* parent, bool value) : QObject(parent)
{
    boolVal = value;
    isBool = true;
    isNoVal = false;
}

FormFieldValue::FormFieldValue(QObject* parent) : QObject(parent)
{
    isBool = false;
    isNoVal = true;
}

bool FormFieldValue::getBool() const
{
    Q_ASSERT(isBool);
    Q_ASSERT(!isNoVal);
    return boolVal;
}

QString FormFieldValue::getStr() const
{
    Q_ASSERT(!isBool);
    Q_ASSERT(!isNoVal);
    return strVal;
}

bool FormFieldValue::isNoValue() const
{
    return isNoVal;
}

QString FormFieldValue::stringRepresentation() const
{
    Q_ASSERT(!isNoVal);

    if (isBool)
        { return boolTostring(boolVal); }

    return strVal;
}

QDebug operator<<(QDebug dbg, const FormFieldValue& f)
{
    if (f.isBool)
        { dbg.nospace() << f.boolVal; }
    else if (!f.isNoVal)
        { dbg.nospace() << f.strVal; }
    else
        { dbg.nospace() << "<no value>"; }

    return dbg.space();
}
}
