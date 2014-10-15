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

namespace artemis
{

class ConcolicTargetGenerator : public TargetGenerator
{

public:
    ConcolicTargetGenerator(TraceBuilder* traceBuilder);
    TargetDescriptorConstPtr generateTarget(EventHandlerDescriptorConstPtr eventHandler) const;
    TargetDescriptorConstPtr permuteTarget(EventHandlerDescriptorConstPtr eventHandler,
                                           TargetDescriptorConstPtr oldTarget,
                                           ExecutionResultConstPtr result) const;

private:
    TraceBuilder* mTraceBuilder;

};

}

#endif // CONCOLICTARGETGENERATOR_H
