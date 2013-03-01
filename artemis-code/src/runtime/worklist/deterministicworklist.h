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
#ifndef DETERMINISTICWORKLIST_H
#define DETERMINISTICWORKLIST_H

#include <queue>
#include <vector>

#include <QPair>

#include "strategies/prioritizer/prioritizerstrategy.h"

#include "worklist.h"

using namespace std;

namespace artemis
{

typedef QPair<double, ExecutableConfigurationConstPtr> WorkListItem;

struct WorkListItemComperator
{
    bool operator() (const WorkListItem& lhs, const WorkListItem& rhs)
    {
        return lhs.first < rhs.first;
    }
};

class DeterministicWorkList : public WorkList
{
public:
    DeterministicWorkList(PrioritizerStrategyPtr prioritizer);

    void add(ExecutableConfigurationConstPtr configuration, AppModelConstPtr appmodel);
    ExecutableConfigurationConstPtr remove();

    void reprioritize(AppModelConstPtr appmodel);

    int size();
    bool empty();

    QString toString() const;

private:
    // mutable here is a hack to support toString
    mutable priority_queue<WorkListItem, vector<WorkListItem>, WorkListItemComperator> mQueue;
    PrioritizerStrategyPtr mPrioritizer;

};

}

#endif // DETERMINISTICWORKLIST_H
