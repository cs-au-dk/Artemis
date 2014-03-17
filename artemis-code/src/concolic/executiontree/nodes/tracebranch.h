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

#include "trace.h"

#include <QSource>

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
    friend class TraceClassifier; // Takes address of mBranchTrue and mBranchFalse and uses this to modify them directly. It seemed even more of a hack to add getTrueBranchPtr() to the interface.

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

    inline uint getSourceOffset()
    {
        return mSourceOffset;
    }

    inline QSource* getSource()
    {
        return mSource;
    }

    inline uint getLinenumber()
    {
        return mLinenumber;
    }

protected:
    TraceBranch(uint sourceOffset, QSource* source, uint linenumber); // we should only use the concrete or symbolic subclasses

    uint mSourceOffset;
    QSource* mSource;
    uint mLinenumber;

    TraceNodePtr mBranchTrue;
    TraceNodePtr mBranchFalse;
};

typedef QSharedPointer<TraceBranch> TraceBranchPtr;

}

#endif // TRACEBRANCH_H
