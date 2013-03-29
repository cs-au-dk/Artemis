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

#include <queue>
#include <utility>

#include "JavaScriptCore/wtf/ExportMacros.h"
#include "JavaScriptCore/bytecode/CodeBlock.h"
#include "JavaScriptCore/interpreter/CallFrame.h"

#include "domtraversal.h"

namespace Symbolic
{

/**
 * Visit all nodes in a breadth first manner, except for the initial root node (JSGlobalObject)
 *
 * JSObjects are only visited once.
 **/
void DomTraversal::traverseDom(JSC::CallFrame* callFrame, DomTraversal* callback)
{
    JSC::CodeBlock* codeBlock = callFrame->codeBlock();
    JSC::JSGlobalObject* jsGlobalObject = codeBlock->globalObject();
    JSC::JSGlobalData* jsGlobalData = &callFrame->globalData();

    typedef std::pair<JSC::JSObject*, std::string> worklist_item_t;

    std::tr1::unordered_set<JSC::JSObject*> visited;
    std::queue<worklist_item_t> worklist;

    worklist.push(std::make_pair<JSC::JSObject*, std::string>(jsGlobalObject, ""));

    while (!worklist.empty()) {
        worklist_item_t item = worklist.front();
        worklist.pop();

        JSC::JSObject* jsObject = item.first;
        std::string path = item.second;

        JSC::PropertyNameArray propertyNames(jsGlobalData);
        JSC::JSObject::getPropertyNames(jsObject, callFrame, propertyNames, JSC::IncludeDontEnumProperties);

        JSC::PropertyNameArrayData::PropertyNameVector::const_iterator iter = propertyNames.data()->propertyNameVector().begin();
        JSC::PropertyNameArrayData::PropertyNameVector::const_iterator end = propertyNames.data()->propertyNameVector().end();

        for (; iter != end; ++iter) {
            JSC::PropertySlot property;
            jsObject->getPropertySlot(callFrame, *iter, property);

            if (strcmp("__qt_sender__", iter->ustring().ascii().data()) == 0) {
                continue;
            }

            std::string propertyPath = (path.size() == 0 ? "" : path +  ".") + std::string(iter->ustring().ascii().data());
            JSC::JSValue propertyValue = property.getValue(callFrame, *iter);

            if (!propertyValue.isObject()) {
                callback->domNodeTraversalCallback(callFrame, propertyPath, propertyValue);
                continue;
            }

            JSC::JSObject* propertyObject = propertyValue.toObject(callFrame);

            if (visited.find(propertyObject) != visited.end()) {
                continue;
            }

            visited.insert(propertyObject);

            // blacklisted paths
            //if (path.compare("document.defaultView") == 0 ||
            //        path.compare("document.all") == 0 ||
            //        path.compare("document.scripts") == 0) {
            //    continue;
            //}

            bool mayTraverse = callback->domNodeTraversalCallback(callFrame, propertyPath, propertyValue);

            if (mayTraverse) {
                worklist.push(std::make_pair<JSC::JSObject*, std::string>(propertyObject, propertyPath));
            }
        }
    }
}

}

#endif
