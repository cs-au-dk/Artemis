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
    JSC::CodeBlock* codeBlock = callFrame->codeBlock();

    JSC::JSGlobalData* jsGlobalData = &callFrame->globalData();
    JSC::JSGlobalObject* jsGlobalObject = codeBlock->globalObject();

    visited_t visited;

    buildRegistryVisit(jsGlobalData, callFrame, jsGlobalObject, &visited, "");
}

void NativeLookup::buildRegistryVisit(JSC::JSGlobalData* jsGlobalData, JSC::CallFrame* callFrame, JSC::JSObject* jsObject, visited_t* visited, std::string path) {

    visited_t::iterator visititer = visited->find(jsObject);

    if (visititer != visited->end()) {
        return;
    }

    // force the search to look into .window (such that we can get some more saying paths)
    if (path.compare("document.defaultView") == 0 ||
            path.compare("document.all") == 0 ||
            path.compare("document.scripts") == 0) {
        return;
    }

    visited->insert(jsObject);

    JSC::PropertyNameArray propertyNames(jsGlobalData);
    JSC::JSObject::getPropertyNames(jsObject, callFrame, propertyNames, JSC::ExcludeDontEnumProperties);

    JSC::PropertyNameArrayData::PropertyNameVector::const_iterator iter = propertyNames.data()->propertyNameVector().begin();
    JSC::PropertyNameArrayData::PropertyNameVector::const_iterator end = propertyNames.data()->propertyNameVector().end();

    for (; iter != end; ++iter) {
        JSC::PropertySlot property;
        jsObject->getPropertySlot(callFrame, *iter, property);

        JSC::JSValue value = property.getValue(callFrame, *iter);

        std::string newpath = (path.size() == 0 ? "" : path +  ".") + std::string(iter->ustring().ascii().data());

        JSC::CallData callData;
        JSC::CallType callType = JSC::getCallData(value, callData);

        if (callType == JSC::CallTypeHost) {

            JSC::native_function_ID_t nativeFunctionID = (JSC::native_function_ID_t)callData.native.function;

            const NativeFunction* nativeFunction = find(nativeFunctionID);

            if (nativeFunction == NULL || nativeFunction->getName().size() > newpath.size()) {
                mNativeFunctionMap.insert(std::make_pair<JSC::native_function_ID_t, NativeFunction>(nativeFunctionID, NativeFunction(newpath)));
            }
        }

        if (value.isObject()) {
            buildRegistryVisit(jsGlobalData, callFrame, value.toObject(callFrame), visited, newpath);
        }
    }
}

}

#endif
