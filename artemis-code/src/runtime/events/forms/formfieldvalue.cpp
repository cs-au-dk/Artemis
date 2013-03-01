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
