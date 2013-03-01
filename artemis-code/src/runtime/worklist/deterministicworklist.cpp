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

DeterministicWorkList::DeterministicWorkList(PrioritizerStrategyPtr prioritizer) :
    WorkList(),
    mPrioritizer(prioritizer)
{
}

void DeterministicWorkList::add(ExecutableConfigurationConstPtr configuration, AppModelConstPtr appmodel)
{
    mQueue.push(WorkListItem(mPrioritizer->prioritize(configuration, appmodel), configuration));
}

ExecutableConfigurationConstPtr DeterministicWorkList::remove()
{
    Q_ASSERT(!mQueue.empty());

    ExecutableConfigurationConstPtr configuration = mQueue.top().second;
    mQueue.pop();

    return configuration;
}

void DeterministicWorkList::reprioritize(AppModelConstPtr appmodel)
{
    QList<WorkListItem> tmps;

    while (!mQueue.empty()) {
        tmps.append(mQueue.top());
        mQueue.pop();
    }

    foreach (WorkListItem item, tmps) {
        item.first = mPrioritizer->prioritize(item.second, appmodel);
        mQueue.push(item);
    }
}

int DeterministicWorkList::size()
{
    return mQueue.size();
}

bool DeterministicWorkList::empty()
{
    return mQueue.empty();
}

QString DeterministicWorkList::toString() const
{
    // We can't iterate over a priority_queue, thus the ugliness here
    // TODO find a priority_queue implementation supporting iteration

    QList<WorkListItem> tmps;

    while (!mQueue.empty()) {
        tmps.append(mQueue.top());
        mQueue.pop();
    }

    QString output;

    foreach (WorkListItem item, tmps) {
        mQueue.push(item);
        output += QString::number(item.first) + QString(" => ") + item.second->toString() + QString("\n");
    }

    return output;
}

}
