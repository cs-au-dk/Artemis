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

#include <iostream>
#include <assert.h>
#include <util/randomutil.h>

#include <QSet>
#include <QList>

#include "runtime/input/forms/forminputcollection.h"

#include "constantstringforminputgenerator.h"

namespace artemis
{

ConstantStringFormInputGenerator::ConstantStringFormInputGenerator(QList<QString> excludedFormFields) :
    FormInputGenerator(excludedFormFields)
{

}

/**
 * This strategy relies on constant strings extracted from the latest JavaScript run for text input fields.
 *
 * All other field types are handled using the random strategy.
 */
FormInputCollectionPtr ConstantStringFormInputGenerator::generateFormFields(QSet<FormFieldDescriptorConstPtr> fields,
                                                                            ExecutionResultConstPtr executionResult) const
{
    QList<FormInputPair> inputs;

    foreach(QSharedPointer<const FormFieldDescriptor> field, fields) {

        if (mExcludedFormFields.contains(field->getDomElement()->getId())) {
            continue;
        }

        switch (field->getType()) {
        case TEXT:
            if (executionResult->getJavascriptConstantsObservedForLastEvent().size() == 0) {
                inputs.append(FormInputPair(field, generateRandomString(10)));
            } else {
                inputs.append(FormInputPair(field, pickRand(executionResult->getJavascriptConstantsObservedForLastEvent())));
            }
            break;

        case BOOLEAN:
            inputs.append(FormInputPair(field, randomBool() ? "true" : "false"));
            break;

        case FIXED_INPUT:
            inputs.append(FormInputPair(field, pickRand(field->getInputOptions())));
            break;

        default:
            inputs.append(FormInputPair(field, ""));
        }
    }

    return QSharedPointer<FormInputCollection>(new FormInputCollection(inputs));
}

}
