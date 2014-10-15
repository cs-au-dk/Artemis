/*
 * Copyright 2014 Aarhus University
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

#include "concolictarget.h"
#include "concolic/pathcondition.h"

#include "concolictargetgenerator.h"

namespace artemis {

ConcolicTargetGenerator::ConcolicTargetGenerator(TraceBuilder* traceBuilder)
    : TargetGenerator()
    , mTraceBuilder(traceBuilder)
{
}

TargetDescriptorConstPtr ConcolicTargetGenerator::generateTarget(EventHandlerDescriptorConstPtr eventHandler) const
{
    // create a context and save a reference in the returned target...
    // this reference can then be pulled out from oldTarget in permuteTarget below.

    // This method should do the naive solution and return a target == base handler (see legacy target impl.)

    return TargetDescriptorConstPtr(new ConcolicTarget(eventHandler));
}

TargetDescriptorConstPtr ConcolicTargetGenerator::permuteTarget(EventHandlerDescriptorConstPtr eventHandler,
                                       TargetDescriptorConstPtr oldTarget,
                                       ExecutionResultConstPtr result) const
{

    PathConditionPtr pc = PathCondition::createFromTrace(mTraceBuilder->trace());

    // now the fun begins. We have a reference to the trace builder, and the symbolic "context" in oldTarget. Now check if any
    // constraints exist, if so return a new target to try out. If no interesting targets exist then return NULL as below.

    // If a target is found, then return a ConcolicTarget with the context and a representation (xpath) of the target. The
    // runtime will call "get" on the target in the next iteration and use the xpath to find the real target.

    // Notice that this function can be called multiple times with the same "oldTarget" and "result", because of how Artemis functions.
    // We should only return the new interesting target once, and otherwise NULL.

    // The symbolic variable for the target will be TARGET_0. We only start the symbolic session for the last event to be executed, and
    // permuteTarget is only called for the last event in an event sequence! -- we can assume that the event sequence reaching this event
    // is constant.

    return TargetDescriptorConstPtr(NULL);

}

}
