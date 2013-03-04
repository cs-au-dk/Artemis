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
#ifndef FORMINPUT_H
#define FORMINPUT_H

#include <QSet>
#include <QPair>

#include "formfield.h"
#include "formfieldvalue.h"

namespace artemis
{

typedef QPair<QSharedPointer<const FormField>, const FormFieldValue*> input_t; // workaround for foreach comma bug

class FormInput
{

public:
    FormInput(QSet<QPair<QSharedPointer<const FormField>, const FormFieldValue*> >& inputs);

    QSet<QSharedPointer<const FormField> > getFields() const;
    QSet<QPair<QSharedPointer<const FormField>, const FormFieldValue*> > getInputs() const;
    void writeToPage(ArtemisWebPagePtr) const;

    QDebug friend operator<<(QDebug dbg, FormInput* f);

private:
    QSet<QPair<QSharedPointer<const FormField>, const FormFieldValue*> > mInputs;

};

}

#endif // FORMINPUT_H
