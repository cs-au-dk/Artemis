
#include <utility>
#include <iostream>

#include "JavaScriptCore/wtf/ExportMacros.h"
#include "JavaScriptCore/bytecode/CodeBlock.h"
#include "JavaScriptCore/interpreter/CallFrame.h"

#include "JavaScriptCore/runtime/MathObject.h"
#include "WebCore/generated/"

#include "natives.h"

#include "nativelookup.h"

namespace SymbolicExecution
{

NativeLookup::NativeLookup()
{

    mNativeFunctionMap.insert(std::make_pair<JSC::native_function_ID_t, NativeFunction>(
                                  (JSC::native_function_ID_t)JSC::mathProtoFuncAbs,
                                  NativeFunction("Math.abs")));

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

void NativeLookup::assertConsistency(JSC::CallFrame* callFrame)
{
    JSC::CodeBlock* codeBlock = callFrame->codeBlock();

    JSC::JSGlobalData* jsGlobalData = &callFrame->globalData();
    JSC::JSGlobalObject* jsGlobalObject = codeBlock->globalObject();

    visited_t visited;

    assertConsistencyVisit(jsGlobalData, callFrame, jsGlobalObject, &visited, "");
}

void NativeLookup::assertConsistencyVisit(JSC::JSGlobalData* jsGlobalData, JSC::CallFrame* callFrame, JSC::JSObject* jsObject, visited_t* visited, std::string path) {

    visited_t::iterator visititer = visited->find(jsObject);

    if (visititer != visited->end()) {
        return;
    }

    // force the search to look into .window (such that we can get some more saying paths)
    if (path.compare(".document.defaultView") == 0 ||
            path.compare(".document.all") == 0 ||
            path.compare(".document.scripts") == 0) {
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

        std::string newpath = path + "." + std::string(iter->ustring().ascii().data());

        JSC::CallData callData;
        JSC::CallType callType = JSC::getCallData(value, callData);



        if (callType == JSC::CallTypeHost) {

            //std::cout << (JSC::native_function_ID_t)callData.native.function << " " << newpath << std::endl;

            if (find((JSC::native_function_ID_t)callData.native.function) == NULL) {
                std::cerr << "Error: Could not find native function bound at " << newpath << std::endl;
                exit(1);
            }
        }

        if (value.isObject()) {
            assertConsistencyVisit(jsGlobalData, callFrame, value.toObject(callFrame), visited, newpath);
        }
    }
}

}
