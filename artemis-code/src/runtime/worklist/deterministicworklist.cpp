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
