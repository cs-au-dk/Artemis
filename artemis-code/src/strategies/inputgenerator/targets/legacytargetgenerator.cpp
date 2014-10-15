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

#include "strategies/inputgenerator/targets/legacytarget.h"

#include "legacytargetgenerator.h"

namespace artemis {

TargetDescriptorConstPtr LegacyTargetGenerator::generateTarget(EventHandlerDescriptorConstPtr eventHandler) const
{
    return TargetDescriptorConstPtr(new LegacyTarget(eventHandler));
}

TargetDescriptorConstPtr LegacyTargetGenerator::permuteTarget(EventHandlerDescriptorConstPtr eventHandler,
                                                              TargetDescriptorConstPtr oldTarget,
                                                              ExecutionResultConstPtr result) const
{
    return TargetDescriptorConstPtr(NULL);
}

} // END NAMESPACE
