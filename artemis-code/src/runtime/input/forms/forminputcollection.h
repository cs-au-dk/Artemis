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

#ifndef FORMINPUT_H
#define FORMINPUT_H

#include <QList>
#include <QPair>
#include <QString>
#include <QSharedPointer>

#include "formfielddescriptor.h"
#include "formfieldinjector.h"

namespace artemis
{

typedef QPair<FormFieldDescriptorConstPtr, QString> FormInputPair;

/**
 * A collection of <form input, value> pairs used to inject concrete values into a web page
 */
class FormInputCollection
{

public:
    FormInputCollection(const QList<FormInputPair>& inputs);

    QSet<FormFieldDescriptorConstPtr> getFields() const;

    inline QList<FormInputPair> getInputs() const {
        return mInputs;
    }

    void writeToPage(ArtemisWebPagePtr) const;

    QDebug friend operator<<(QDebug dbg, FormInputCollection* f);

private:
    QList<FormInputPair> mInputs;

};

typedef QSharedPointer<FormInputCollection> FormInputCollectionPtr;
typedef QSharedPointer<const FormInputCollection> FormInputCollectionConstPtr;

}

#endif // FORMINPUT_H
