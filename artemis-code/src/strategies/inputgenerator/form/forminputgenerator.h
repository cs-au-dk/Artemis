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
#ifndef FORMINPUTGENERATOR_H
#define FORMINPUTGENERATOR_H

#include <QObject>
#include <QSet>
#include <QSharedPointer>

#include "runtime/input/forms/formfield.h"
#include "runtime/input/forms/forminput.h"
#include "runtime/browser/executionresult.h"

namespace artemis
{

class FormInputGenerator
{

public:
    FormInputGenerator() {}
    virtual ~FormInputGenerator() {}

    virtual QSharedPointer<FormInput> generateFormFields(QObject* parent,
                                                         QSet<QSharedPointer<const FormField> > fi,
                                                         QSharedPointer<const ExecutionResult> executionResult) const = 0;
};

}

#endif // FORMINPUTGENERATOR_H
