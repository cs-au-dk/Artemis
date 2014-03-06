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

    QString getString() {
        assert(isString());
        return value.toString();
    }
    bool getBool() {
        assert(!isString());
        return value.toBool();
    }
    bool isString() { // Returns true for strings, false for bools.
        return value.type() == QVariant::String;
    }

private:
    QVariant value;
};


} //namespace artemis
#endif // INJECTIONVALUE_H
