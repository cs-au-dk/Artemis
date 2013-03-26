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

#ifndef NATIVELOOKUP_H
#define NATIVELOOKUP_H

#ifdef ARTEMIS

#include <tr1/unordered_map>
#include <tr1/unordered_set>

#include "nativefunction.h"

namespace JSC {
    class ExecState;
}

namespace Symbolic
{

class NativeLookup
{

public:
    NativeLookup();

    const NativeFunction* find(JSC::native_function_ID_t functionID);
    void buildRegistry(JSC::ExecState* callFrame);

private:

    typedef std::tr1::unordered_set<JSC::JSCell*> visited_t;
    void buildRegistryVisit(JSC::JSGlobalData* jsGlobalData, JSC::CallFrame* callFrame, JSC::JSObject* jsObject, visited_t* visited, std::string path);

    typedef std::tr1::unordered_map<JSC::native_function_ID_t, NativeFunction> function_map_t;
    function_map_t mNativeFunctionMap;

};

}

#endif
#endif // NATIVELOOKUP_H
