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

#include "entrypoints.h"

#ifndef MOCKENTRYPOINTDETECTOR_H
#define MOCKENTRYPOINTDETECTOR_H

namespace artemis
{


/**
 * An entry-point finder which hard-codes known entry points for specific sites.
 * This is used for testing the concolic mode before we have a robust real
 * implementation for finding and choosing entry points.
 */
class MockEntryPointDetector : public EntryPointDetector
{
public:
    MockEntryPointDetector(ArtemisWebPagePtr page);

    // Chooses a single entry point on the page. Can return NULL if it does not find a suitable entry point.
    EventHandlerDescriptor* choose(ExecutionResultPtr result);
};



} //namespace artemis

#endif // MOCKENTRYPOINTDETECTOR_H
