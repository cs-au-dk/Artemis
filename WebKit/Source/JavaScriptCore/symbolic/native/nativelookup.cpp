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

#ifdef ARTEMIS

#include <utility>
#include <iostream>

#include "JavaScriptCore/wtf/ExportMacros.h"
#include "JavaScriptCore/bytecode/CodeBlock.h"
#include "JavaScriptCore/interpreter/CallFrame.h"

#include "natives.h"

#include "nativelookup.h"

namespace Symbolic
{

NativeLookup::NativeLookup()
{
}

const NativeFunction* NativeLookup::find(JSC::native_function_ID_t functionID)
{
    function_map_t::iterator iter = mNativeFunctionMap.find(functionID);
    if (iter != mNativeFunctionMap.end()) {
        return &iter->second;
    } else {
        return NULL;
    }
}

void NativeLookup::buildRegistry(JSC::CallFrame* callFrame)
{
    DomTraversal::traverseDom(callFrame, this);
}

bool NativeLookup::domNodeTraversalCallback(std::string path, JSC::JSValue jsValue)
{
    if (jsValue.isObject()) {
        JSC::CallData callData;
        JSC::CallType callType = JSC::getCallData(jsValue, callData);

        if (callType == JSC::CallTypeHost) {

            JSC::native_function_ID_t nativeFunctionID = (JSC::native_function_ID_t)callData.native.function;

            const NativeFunction* nativeFunction = find(nativeFunctionID);

            if (nativeFunction == NULL || nativeFunction->getName().size() > path.size()) {
                mNativeFunctionMap.insert(std::make_pair<JSC::native_function_ID_t, NativeFunction>(nativeFunctionID, NativeFunction(path)));
            }
        }
    }

    return true;
}

}

#endif
