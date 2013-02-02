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

#include <stdlib.h>

#include "deterministicworklist.h"

namespace artemis
{

DeterministicWorkList::DeterministicWorkList(QObject* parent) :
    WorkList(parent)
{
    queue.clear();
    largestPri = 0;
}

void DeterministicWorkList::add(QSharedPointer<ExecutableConfiguration> e, int priority)
{
    QSet<QSharedPointer<ExecutableConfiguration> > set = queue.value(priority);
    set.insert(e);

    if (priority > largestPri) {
        largestPri = priority;
    }
}

QSharedPointer<ExecutableConfiguration> DeterministicWorkList::remove()
{
    QSet<QSharedPointer<ExecutableConfiguration> > set = queue.value(largestPri);
    Q_ASSERT(!set.isEmpty());

    QSharedPointer<ExecutableConfiguration> result = set.toList().at(rand() % set.size());
    set.remove(result);

    if (set.isEmpty()) {
        queue.remove(largestPri);
        largestPri = queue.empty() ? 0 : queue.keys().last();
    }

    return result;
}

bool DeterministicWorkList::allZeroPriority()
{
    return largestPri == 0;
}

int DeterministicWorkList::size()
{
    int res = 0;
    foreach(int k, queue.keys()) {
        res += queue.value(k).size();
    }
    return res;
}

bool DeterministicWorkList::empty()
{
    return queue.empty();
}

bool DeterministicWorkList::contains(QSharedPointer<ExecutableConfiguration> e)
{
    foreach(int k, queue.keys()) {
        if (queue.value(k).contains(e)) {
            return true;
        }
    }
    return false;
}

void DeterministicWorkList::newPriority(QSharedPointer<ExecutableConfiguration> e, int priority)
{
    foreach(int k, queue.keys()) {
        QSet<QSharedPointer<ExecutableConfiguration> > set = queue.value(k);

        if (set.contains(e)) {
            set.remove(e);
        }
    }
    add(e, priority);
}

}
