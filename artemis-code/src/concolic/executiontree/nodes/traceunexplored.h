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

#ifndef TRACEUNEXPLORED_H
#define TRACEUNEXPLORED_H

#include "trace.h"

namespace artemis {

/**
 * This is just a placeholder for unexplored parts of the tree.
 *
 * This node is a singleton node.
 */
class TraceUnexplored : public TraceNode
{

public:

    /**
     * For performance reasons we only generate a single unexplored trace node such
     * that we can quickly get and discard these without trashing our memory.
     */
    static QSharedPointer<TraceUnexplored> getInstance();

    void accept(TraceVisitor* visitor);
    bool isEqualShallow(const QSharedPointer<const TraceNode>& other);
    ~TraceUnexplored() {}

    // This must be a pointer, it will not compile as a value
    static QSharedPointer<TraceUnexplored>* mInstance;

protected:
    TraceUnexplored() {}



};

typedef QSharedPointer<TraceUnexplored> TraceUnexploredPtr;


}

#endif // TRACEUNEXPLORED_H
