
#include <iostream>
#include <tr1/unordered_set>

#include "JavaScriptCore/wtf/ExportMacros.h"
#include "JavaScriptCore/bytecode/CodeBlock.h"
#include "JavaScriptCore/interpreter/CallFrame.h"

#include "symbolicinterpreter.h"

#ifdef ARTEMIS

namespace SymbolicExecution
{

typedef std::tr1::unordered_set<JSC::JSCell*> visited_t;

void visitJsObject(JSC::JSGlobalData* jsGlobalData, JSC::CallFrame* callFrame, JSC::JSObject* jsObject, visited_t* visited, uint depth, std::string path) {

    visited_t::iterator visititer = visited->find(jsObject);

    if (visititer != visited->end() || depth > 5) {
        return;
    }

    visited->insert(jsObject);

    JSC::PropertyNameArray propertyNames(jsGlobalData);
    JSC::JSObject::getPropertyNames(jsObject, callFrame, propertyNames, JSC::IncludeDontEnumProperties);

    // property traversal

    JSC::PropertyNameArrayData::PropertyNameVector::const_iterator iter = propertyNames.data()->propertyNameVector().begin();
    JSC::PropertyNameArrayData::PropertyNameVector::const_iterator end = propertyNames.data()->propertyNameVector().end();

    for (; iter != end; ++iter) {
        JSC::PropertySlot property;
        jsObject->getPropertySlot(callFrame, *iter, property);

        JSC::JSValue value = property.getValue(callFrame, *iter);

        std::string newpath = path + "." + std::string(iter->ustring().ascii().data());

        std::cout << newpath << " (objct = " << value.isObject() << ")" << std::endl;

        if (value.isObject()) {
            visitJsObject(jsGlobalData, callFrame, value.toObject(callFrame), visited, depth+1, newpath);
        }
    }
}

SymbolicInterpreter::SymbolicInterpreter() : ArtemisIL()
{
}

void SymbolicInterpreter::ail_call(JSC::CallFrame*, const JSC::Instruction*)
{
    std::cout << "AIL_CALL" << std::endl;
}

void SymbolicInterpreter::ail_call_native(JSC::CallFrame* callFrame, const JSC::Instruction*,
                                          JSC::native_function_ID_t functionID)
{
    JSC::CodeBlock* codeBlock = callFrame->codeBlock();

    JSC::JSGlobalData* jsGlobalData = &callFrame->globalData();
    JSC::JSGlobalObject* jsGlobalObject = codeBlock->globalObject();

    visited_t visited;

    visitJsObject(jsGlobalData, callFrame, jsGlobalObject, &visited, 0, "");


    //JSC::SymbolTable symbolTable = jsGlobalObject->symbolTable();

    //JSC::SymbolTable::const_iterator it = symbolTable.begin();
    //JSC::SymbolTable::const_iterator end = symbolTable.end();

    /*for (; it != end; ++it) {
        printf("ROOT.%s\n", JSC::UString(it->first).ascii().data());

        JSC::Identifier ident = JSC::Identifier(&jsGlobalObject->globalData(), it->first);
        JSC::JSValue jsValue = jsGlobalObject->get(callFrame, ident);

        printf("is object == %i\n", jsValue.isObject());

        if (jsValue.isObject()) {

            JSC::JSObject* jsObject = jsValue.toObject(callFrame);
        }
    }*/

    const NativeFunction* nativeFunction = mNativeFunctions.find(functionID);

    if (nativeFunction == NULL) {
        fatalError(codeBlock, "Unknown native function encountered");
    }

    std::cout << "AIL_CALL_NATIVE <" << nativeFunction->getName() << ">" << std::endl;
}

void SymbolicInterpreter::fatalError(JSC::CodeBlock* codeBlock, std::string reason)
{
    std::cerr << reason << std::endl;
    exit(1);
}

}

#endif
