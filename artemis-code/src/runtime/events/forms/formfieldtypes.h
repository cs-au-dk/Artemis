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
#ifndef FORMFIELDTYPES_H
#define FORMFIELDTYPES_H

#include <QString>

namespace artemis
{
enum FormFieldTypes {TEXT, FIXED_INPUT, BOOLEAN, NO_INPUT};

inline QString formFieldTypeTostring(FormFieldTypes f)
{
    switch (f) {
    case TEXT:
        return "TEXT";
    case FIXED_INPUT:
        return "FIXED_INPUT";
    case BOOLEAN:
        return "BOOLEAN";
    case NO_INPUT:
        return "NO_INPUT";
    }

    return "ERROR1";
}

FormFieldTypes getTypeFromAttr(QString typeAttr);

}

#endif // FORMFIELDTYPES_H
