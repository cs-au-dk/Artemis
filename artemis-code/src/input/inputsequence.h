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
#ifndef INPUTSEQUENCE_H
#define INPUTSEQUENCE_H

#include <QObject>
#include <QList>

#include "events/eventhandlerdescriptor.h"
#include "baseinput.h"

namespace artemis
{

class InputSequence
{
public:
    InputSequence(const QList<BaseInput*>& sequence);
    InputSequence(const InputSequence& sequence);
    InputSequence();

    ~InputSequence();

    InputSequence new_last(BaseInput* new_last);
    InputSequence extend(BaseInput* new_last);
    bool is_empty() const;
    BaseInput* get_last() const;
    QList<BaseInput*> to_list() const;

    uint hashcode() const;
    bool operator==(const InputSequence& other) const;
    QDebug friend operator<<(QDebug dbg, const InputSequence& e);
    InputSequence &operator=(const InputSequence& other);

private:
    QList<BaseInput*> mSequence;
};

}
#endif // INPUTSEQUENCE_H
