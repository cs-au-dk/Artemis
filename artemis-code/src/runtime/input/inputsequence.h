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

#ifndef INPUTSEQUENCE_H
#define INPUTSEQUENCE_H

#include <QList>

#include "baseinput.h"

namespace artemis
{

class InputSequence
{

public:
    InputSequence();
    InputSequence(const QList<QSharedPointer<const BaseInput> >& sequence);

    QSharedPointer<const InputSequence> replaceLast(QSharedPointer<const BaseInput> newLast) const;
    QSharedPointer<const InputSequence> extend(QSharedPointer<const BaseInput> newLast) const;

    bool isEmpty() const;
    QSharedPointer<const BaseInput> getLast() const;
    const QList<QSharedPointer<const BaseInput> > toList() const;

    QString toString() const;

private:
    const QList<QSharedPointer<const BaseInput> > mSequence;
};

typedef QSharedPointer<InputSequence> InputSequencePtr;
typedef QSharedPointer<const InputSequence> InputSequenceConstPtr;

}
#endif // INPUTSEQUENCE_H
