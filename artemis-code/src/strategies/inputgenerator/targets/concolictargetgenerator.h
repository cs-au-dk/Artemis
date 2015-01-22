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

#ifndef CONCOLICTARGETGENERATOR_H
#define CONCOLICTARGETGENERATOR_H

#include "strategies/inputgenerator/targets/targetgenerator.h"
#include "strategies/inputgenerator/targets/jquerylistener.h"
#include "concolic/executiontree/tracebuilder.h"
#include "runtime/options.h"
#include "concolic/solver/solution.h"
#include "model/domsnapshotstorage.h"

namespace artemis
{

class ConcolicTargetGenerator : public TargetGenerator
{

public:
    ConcolicTargetGenerator(Options options, TraceBuilder* traceBuilder, DomSnapshotStoragePtr domSnapshotStorage);
    TargetDescriptorConstPtr generateTarget(EventHandlerDescriptorConstPtr eventHandler) const;
    TargetDescriptorConstPtr permuteTarget(EventHandlerDescriptorConstPtr eventHandler,
                                           TargetDescriptorConstPtr oldTarget,
                                           ExecutionResultConstPtr result) const;

protected:
    Options mOptions;
    TraceBuilder* mTraceBuilder;
    mutable uint mTreeIdx;
    DomSnapshotStoragePtr mDomSnapshotStorage;

    void printSolution(const SolutionPtr solution) const;
    void outputTree(TraceNodePtr tree, QString eventName, uint count) const;

};

}

#endif // CONCOLICTARGETGENERATOR_H
