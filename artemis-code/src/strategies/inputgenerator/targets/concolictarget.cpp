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

namespace artemis
{

ConcolicTarget::ConcolicTarget(EventHandlerDescriptorConstPtr eventHandler, QString targetXPath, ConcolicAnalysisPtr analysis, ConcolicAnalysis::ExplorationHandle explorationTarget)
    : TargetDescriptor(eventHandler)
    , mTargetXPath(targetXPath)
    , mAnalysis(analysis)
    , mExplorationTarget(explorationTarget)
{
}

QWebElement ConcolicTarget::get(ArtemisWebPagePtr page) const
{
    // TODO: If mTargetXPath is non-empty, then use that to find the appropriate target instead!


    // legacy impl.
    return mEventHandler->getDomElement()->getElement(page);
}

ConcolicAnalysisPtr ConcolicTarget::getAnalysis() const
{
    return mAnalysis;
}

ConcolicAnalysis::ExplorationHandle ConcolicTarget::getExplorationTarget() const
{
    return mExplorationTarget;
}

}
