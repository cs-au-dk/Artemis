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

#include "runtime/input/forms/forminputcollection.h"

#include "staticforminputgenerator.h"

namespace artemis
{

StaticFormInputGenerator::StaticFormInputGenerator(QList<QString> excludedFormFields) :
    FormInputGenerator(excludedFormFields)
{

}

FormInputCollectionPtr StaticFormInputGenerator::generateFormFields(QSet<FormFieldDescriptorConstPtr> fields,
                                                                    ExecutionResultConstPtr) const
{
    QList<FormInputPair> inputs;

    foreach(FormFieldDescriptorConstPtr field, fields) {

        if (mExcludedFormFields.contains(field->getDomElement()->getId())) {
            continue;
        }

        switch (field->getType()) {
        case TEXT:
            inputs.append(FormInputPair(field, generateRandomString(10)));
            break;
        case BOOLEAN:
            inputs.append(FormInputPair(field, randomBool() ? "true" : "false"));
            break;
        case FIXED_INPUT:
            if(field->getInputOptions().size()>0){
                inputs.append(FormInputPair(field, pickRand(field->getInputOptions())));
                break;
            }
        default:
            inputs.append(FormInputPair(field, ""));
        }
    }

    return FormInputCollectionPtr(new FormInputCollection(inputs));
}

}
