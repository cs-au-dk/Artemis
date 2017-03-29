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

    virtual void setChild(int position, TraceNodePtr node) {
        assert(position == 0 || position == 1);
        if (position == 0) {
            setFalseBranch(node);
        } else {
            setTrueBranch(node);
        }
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
