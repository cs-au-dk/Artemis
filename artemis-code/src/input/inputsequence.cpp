/*
 Copyright 2011 Simon Holm Jensen. All rights reserved.

 Redistribution and use in source and binary forms, with or without modification, are
 permitted provided that the following conditions are met:

 1. Redistributions of source code must retain the above copyright notice, this list of
 conditions and the following disclaimer.

 2. Redistributions in binary form must reproduce the above copyright notice, this list
 of conditions and the following disclaimer in the documentation and/or other materials
 provided with the distribution.

 THIS SOFTWARE IS PROVIDED BY SIMON HOLM JENSEN ``AS IS'' AND ANY EXPRESS OR IMPLIED
 WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND
 FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL <COPYRIGHT HOLDER> OR
 CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
 ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
 ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

 The views and conclusions contained in the software and documentation are those of the
 authors and should not be interpreted as representing official policies, either expressed
 or implied, of Simon Holm Jensen
 */
#include <QHash>

#include "artemisglobals.h"

#include "inputsequence.h"

namespace artemis
{

InputSequence::InputSequence(const QList<BaseInput*>& sequencee)
{
    mSequence += sequencee;
}

InputSequence::InputSequence()
{
    mSequence.clear();
}

InputSequence::~InputSequence()
{
    //sequence->free();
}

InputSequence::InputSequence(const InputSequence &seq)
{
    mSequence += seq.mSequence;
}

InputSequence InputSequence::new_last(BaseInput* new_last)
{
    QList<BaseInput*> res(mSequence);
    res.removeLast();
    res.append(new_last);
    return InputSequence(res);
}

InputSequence InputSequence::extend(BaseInput* new_last)
{
    QList<BaseInput*> res(mSequence);
    res.append(new_last);
    return InputSequence(res);
}

bool InputSequence::is_empty() const
{
    return mSequence.empty();
}

BaseInput *InputSequence::get_last() const
{
    return mSequence.last();
}

QList<BaseInput*> InputSequence::to_list() const
{
    return mSequence;
}

bool InputSequence::operator ==(const InputSequence& other) const
{
    return mSequence == (other.mSequence);
}

uint InputSequence::hashcode() const
{
    return qHash(mSequence);
}

QDebug operator<<(QDebug dbg, const InputSequence &e)
{
    dbg.nospace() << e.mSequence;
    return dbg.space();
}

InputSequence &InputSequence::operator=(const InputSequence &other)
{
    mSequence.clear();
    mSequence += other.mSequence;
    return *this;
}

}
