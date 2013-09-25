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

#ifndef FORMFIELD_H
#define FORMFIELD_H

#include <QSet>
#include <QString>
#include <QSharedPointer>
#include <QDebug>

#include "util/loggingutil.h"
#include "runtime/input/events/domelementdescriptor.h"

namespace artemis
{

enum FormFieldTypes {
    TEXT, FIXED_INPUT, BOOLEAN, NO_INPUT
};

FormFieldTypes getTypeFromAttr(QString typeAttr);


/**
 * Representation of a form field observed in a concrete execution, including its type, placement and possible options (select).
 */
class FormFieldDescriptor
{

public:
    FormFieldDescriptor(FormFieldTypes fieldType, DOMElementDescriptorConstPtr domElementDescriptor, QSet<QString> inputOptions);
    FormFieldDescriptor(FormFieldTypes fieldType, DOMElementDescriptorConstPtr domElementDescriptor);

    inline const DOMElementDescriptorConstPtr getDomElement() const {
        return mDomElementDescriptor;
    }

    inline FormFieldTypes getType() const {
        return mFieldType;
    }

    inline const QSet<QString> getInputOptions() const {
        return mInputOptions;
    }

    QDebug friend operator<<(QDebug dbg, const FormFieldDescriptor& f);

private:
    const FormFieldTypes mFieldType;
    DOMElementDescriptorConstPtr mDomElementDescriptor;
    const QSet<QString> mInputOptions;

    inline QString formFieldTypeTostring(FormFieldTypes f) const
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

        Log::error("Error: Unknown FormFieldTypes value encountered.");
        exit(1);
    }

};

typedef QSharedPointer<FormFieldDescriptor> FormFieldDescriptorPtr;
typedef QSharedPointer<const FormFieldDescriptor> FormFieldDescriptorConstPtr;

}

#endif // FORMFIELD_H
