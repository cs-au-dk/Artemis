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

#ifndef TARGETGENERATOR_H_
#define TARGETGENERATOR_H_

#include <QSharedPointer>

#include "runtime/input/events/eventhandlerdescriptor.h"

#include "targetdescriptor.h"

namespace artemis
{

/**
 * @brief The TargetGenerator class
 *
 * The TargetGenerator selects the DOM node used as the target argument used when triggering a given event handler. The choice
 * is encoded in the TagetDescriptor.
 *
 * TargetGenerator is called post-execution in iteration A, while TargetDescriptors are used to identify concrete DOM nodes observed
 * at runtime in a later iteration not equal to A (using the get method on TargetDesciptor).
 *
 */
class TargetGenerator
{

public:
    TargetGenerator() {}
    virtual ~TargetGenerator() {}

    virtual TargetDescriptorConstPtr generateTarget(EventHandlerDescriptorConstPtr eventHandler) const = 0;
};

typedef QSharedPointer<const TargetGenerator> TargetGeneratorConstPtr;

} // END NAMESPACE

#endif /* TARGETGENERATOR_H_ */
