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

#include "inputsequence.h"

namespace artemis
{

InputSequence::InputSequence()
{
}

InputSequence::InputSequence(const QList<QSharedPointer<const BaseInput> >& sequence)
    : mSequence(sequence)
{
}

QSharedPointer<const InputSequence> InputSequence::replaceLast(QSharedPointer<const BaseInput> newLast) const
{
    QList<QSharedPointer<const BaseInput> > sequence = mSequence;
    sequence.removeLast();
    sequence.append(newLast);

    return QSharedPointer<const InputSequence>(new InputSequence(sequence));
}

QSharedPointer<const InputSequence> InputSequence::extend(QSharedPointer<const BaseInput> newLast) const
{
    QList<QSharedPointer<const BaseInput> > sequence = mSequence;
    sequence.append(newLast);

    return QSharedPointer<InputSequence>(new InputSequence(sequence));
}

bool InputSequence::isEmpty() const
{
    return mSequence.empty();
}

QSharedPointer<const BaseInput> InputSequence::getLast() const
{
    return mSequence.last();
}

const QList<QSharedPointer<const BaseInput> > InputSequence::toList() const
{
    return mSequence;
}

QString InputSequence::toString() const
{
    QString output;

    foreach (QSharedPointer<const BaseInput> input, mSequence) {
        output += input->toString() + QString(" => ");
    }

    return output;
}

}
