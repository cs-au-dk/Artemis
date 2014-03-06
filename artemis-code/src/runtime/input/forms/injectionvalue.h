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

#ifndef INJECTIONVALUE_H
#define INJECTIONVALUE_H

#include <QVariant>
#include <QDebug>
#include "assert.h"

namespace artemis
{

/**
 * InjectionValue is a thin wrapper around QVariant.
 * This just allows us to enforce that only certain types (QString or bool) are stored in this value.
 */
class InjectionValue
{
public:
    InjectionValue(QString stringValue) : value(stringValue) {}
    InjectionValue(bool boolValue) : value(boolValue) {}
    InjectionValue() : value(QString()) {} // Need default constructor to be able to put InjectionValue into a QMap.

    QString getString() const {
        assert(isString());
        return value.toString();
    }
    bool getBool() const {
        assert(!isString());
        return value.toBool();
    }
    bool isString() const { // Returns true for strings, false for bools.
        return value.type() == QVariant::String;
    }
    QString toString() const { // Used as a printable value for debug output, etc. Should not be used for injection!
        return value.toString();
    }

    QDebug friend operator<<(QDebug dbg, const InjectionValue iv) {
        dbg.nospace() << iv.toString();
        return dbg.space();
    }

private:
    QVariant value;
};


} //namespace artemis
#endif // INJECTIONVALUE_H
