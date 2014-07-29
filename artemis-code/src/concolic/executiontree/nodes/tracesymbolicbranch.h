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

#ifndef TRACESYMBOLICBRANCH_H
#define TRACESYMBOLICBRANCH_H

#include <assert.h>

#include "tracebranch.h"

namespace artemis {

class TraceSymbolicBranch : public TraceBranch
{
public:

    TraceSymbolicBranch(Symbolic::Expression* condition, uint sourceOffset, QSource* source, uint linenumber);
    ~TraceSymbolicBranch() {}

    void accept(TraceVisitor* visitor);
    bool isEqualShallow(const QSharedPointer<const TraceNode>& other);

    inline Symbolic::Expression* getSymbolicCondition() const {
        return mCondition;
    }

    inline bool isDifficult() {
        return mDifficult;
    }

    inline void markDifficult() {
        mDifficult = true;
    }

    inline uint getExplorationIndex() {
        return mExplorationIndex;
    }

    inline bool getExplorationDirection() {
        return mExplorationDirection;
    }

    inline void markExploration(uint index, bool direction) {
        assert(index != 0); // Never set to "not explored"
        //assert(mExplorationIndex == 0); // Never re-set.
        mExplorationIndex = index;
        mExplorationDirection = direction;
    }

private:
    Symbolic::Expression* mCondition; // TODO: MEMORY
    bool mDifficult;

    // Used to add an index to the output graph linking which attempted explorations by the search procedure lead to which explored traces.
    uint mExplorationIndex; // 0 = not chosen for exploration by the search.
    bool mExplorationDirection;
};

typedef QSharedPointer<TraceSymbolicBranch> TraceSymbolicBranchPtr;

}

#endif // TRACESYMBOLICBRANCH_H
