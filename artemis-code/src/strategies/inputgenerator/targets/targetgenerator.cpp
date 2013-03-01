/*
 * Copyright 2012 Aarhus University
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include "jquerytarget.h"

#include "targetgenerator.h"

namespace artemis
{

TargetGenerator::TargetGenerator(QObject* parent,
                                 JQueryListener* jqueryListener) :
    QObject(parent)
{

    mJQueryListener = jqueryListener;
}

TargetGenerator::~TargetGenerator()
{
    // TODO Auto-generated destructor stub
}

TargetDescriptor* TargetGenerator::generateTarget(QObject* parent, const EventHandlerDescriptor* eventHandler)
{

    return new JQueryTarget(parent, eventHandler, mJQueryListener);

}


} // END NAMESPACE
