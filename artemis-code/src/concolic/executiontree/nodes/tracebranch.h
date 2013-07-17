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

#include "trace.h"

#ifndef TRACEBRANCH_H
#define TRACEBRANCH_H

namespace artemis {

/**
 * Abstract base class
 */
class TraceBranch : public TraceNode
{

public:

    // TODO remove and use the set* functions
    friend class TraceBranchDetector; // direct modification of mBranchTrue and mBranchFalse

    ~TraceBranch() {}

    inline TraceNodePtr getTrueBranch()
    {
        return mBranchTrue;
    }

    inline void setTrueBranch(TraceNodePtr node)
    {
        mBranchTrue = node;
    }

    inline TraceNodePtr getFalseBranch()
    {
        return mBranchFalse;
    }

    inline void setFalseBranch(TraceNodePtr node)
    {
        mBranchFalse = node;
    }

protected:
    TraceBranch(); // we should only use the concrete or symbolic subclasses

    TraceNodePtr mBranchTrue;
    TraceNodePtr mBranchFalse;
};

typedef QSharedPointer<TraceBranch> TraceBranchPtr;

}

#endif // TRACEBRANCH_H
