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
#include "JavaScriptCore/heap/Heap.h"

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

        std::string identName = std::string(iter->ustring().ascii().data());

        for (; iter != end; ++iter) {

            if (identName.compare("__qt_sender__") == 0 ||
                    identName.compare("attributes") == 0 ||
                    identName.compare("caller") == 0 ||
                    identName.compare("prototype") == 0) {
                continue;
            }

            std::string propertyPath = (path.size() == 0 ? "" : path +  ".") + identName;

            // blacklisted paths
            if (propertyPath.compare("document.defaultView") == 0 ||
                    propertyPath.compare("document.all") == 0 ||
                    propertyPath.compare("document.scripts") == 0 ||
                    propertyPath.compare("document.activeElement") == 0 ||
                    propertyPath.compare("document.links") == 0 ||
                    propertyPath.compare("$") == 0 ||
                    propertyPath.compare("document.styleSheets") == 0) {
                continue;
            }

            JSC::JSValue propertyValue = jsObject->get(callFrame, *iter);

            if (propertyValue.isObject()) {

                JSC::JSObject* propertyObject = propertyValue.toObject(callFrame);

                if (visited.find(propertyObject) != visited.end()) {
                    continue;
                }

                visited.insert(propertyObject);

                bool mayTraverse = callback->domNodeTraversalCallback(callFrame, propertyPath, propertyValue);

                if (mayTraverse) {
                    worklist.push(std::make_pair<JSC::JSObject*, std::string>(propertyObject, propertyPath));
                }

            } else {
                callback->domNodeTraversalCallback(callFrame, propertyPath, propertyValue);
            }
        }
    }

}

}

#endif
