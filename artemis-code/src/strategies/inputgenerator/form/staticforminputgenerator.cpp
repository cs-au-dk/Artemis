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

#include <assert.h>
#include <util/randomutil.h>

#include <QSet>
#include <QList>

#include "runtime/input/forms/formfieldtypes.h"
#include "runtime/input/forms/forminput.h"

#include "staticforminputgenerator.h"

namespace artemis
{

StaticFormInputGenerator::StaticFormInputGenerator() : FormInputGenerator()
{

}

QSharedPointer<FormInput> StaticFormInputGenerator::generateFormFields(QObject* parent,
                                                                       QSet<QSharedPointer<const FormField> > fields,
                                                                       QSharedPointer<const ExecutionResult>) const
{
    QSet<QPair<QSharedPointer<const FormField>, const FormFieldValue*> > inputs;

    foreach(QSharedPointer<const FormField> field, fields) {

        switch (field->getType()) {
        case TEXT:
            inputs.insert(QPair<QSharedPointer<const FormField>, const FormFieldValue*>(field, new FormFieldValue(parent, generateRandomString(10))));
            break;
        case BOOLEAN:
            inputs.insert(QPair<QSharedPointer<const FormField>, const FormFieldValue*>(field, new FormFieldValue(parent, randomBool())));
            break;
        case FIXED_INPUT:
            inputs.insert(QPair<QSharedPointer<const FormField>, const FormFieldValue*>(field, new FormFieldValue(parent, pickRand(field->getInputOptions()))));
            break;
        default:
            inputs.insert(QPair<QSharedPointer<const FormField>, const FormFieldValue*>(field, new FormFieldValue(parent)));
        }
    }

    return QSharedPointer<FormInput>(new FormInput(inputs));
}

}
