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
