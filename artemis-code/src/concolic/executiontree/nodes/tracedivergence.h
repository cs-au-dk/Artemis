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

#ifndef TRACEDIVERGENCE_H
#define TRACEDIVERGENCE_H

#include "trace.h"

namespace artemis {

/**
 * Marker for parts of the tree where a trace "diverged" from the main tree.
 * That is, the corresponding tree node and trace node did not match.
 *
 * In the concolic mode this is an error (e.g. caused by different code being returned from the server in different
 * iterations).
 *
 * This node is a child of TraceAnnotation because it should be ignored by most operations on the tree (e.g. search).
 * The diverged traces are only useful for after-the-fact analysis.
 *
 * N.B. This node type is special in the sense that it is added as a mid-trace modification by the trace merger and is
 * never generated from the trace recorder or classifier, etc. like other nodes. This means that divergence nodes can
 * appear in the concolic tree but not in the recorded traces, so trace merging must account for this specially.
 */
class TraceDivergence : public TraceAnnotation
{
public:
    void accept(TraceVisitor* visitor)
    {
        visitor->visit(this);
    }

    bool isEqualShallow(const QSharedPointer<const TraceNode>& other)
    {
        return !other.dynamicCast<const TraceDivergence>().isNull();
    }

    virtual void setChild(int position, TraceNodePtr node) {
        assert(position >= 0 && position <= divergedTraces.size());
        if (position == 0) {
            next = node;
        } else {
            divergedTraces[position-1] = node;
        }
    }

    ~TraceDivergence() {}

    QList<TraceNodePtr> divergedTraces;
};

typedef QSharedPointer<TraceDivergence> TraceDivergencePtr;

} // namespace artemis
#endif // TRACEDIVERGENCE_H
