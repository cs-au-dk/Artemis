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

#ifndef FORMINPUTGENERATOR_H
#define FORMINPUTGENERATOR_H

#include <QObject>
#include <QSet>
#include <QSharedPointer>
#include <QList>
#include <QString>

#include "runtime/input/forms/formfielddescriptor.h"
#include "runtime/input/forms/forminputcollection.h"
#include "runtime/browser/executionresult.h"

namespace artemis
{

class FormInputGenerator
{

public:
    FormInputGenerator(QList<QString> excludedFormFields);

    virtual ~FormInputGenerator() {}

    virtual FormInputCollectionPtr generateFormFields(QSet<FormFieldDescriptorConstPtr> fields,
                                                      ExecutionResultConstPtr executionResult) const = 0;
    virtual FormInputCollectionPtr permuteFormFields(QSet<FormFieldDescriptorConstPtr> fields,
                                                     FormInputCollectionConstPtr oldFields,
                                                     ExecutionResultConstPtr executionResult) const = 0;

protected:
    QList<QString> mExcludedFormFields;
};

typedef QSharedPointer<FormInputGenerator> FormInputGeneratorConstPtr;

}

#endif // FORMINPUTGENERATOR_H
