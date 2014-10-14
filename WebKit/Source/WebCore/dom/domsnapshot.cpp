/*
 * Copyright 2014 Aarhus University
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

#include <queue>
#include <sstream>

#include "wtf/ExportMacros.h"
#include "WebCore/dom/Node.h"
#include "WebCore/dom/NodeList.h"
#include "WebCore/dom/Element.h"
#include "wtf/text/AtomicString.h"
#include "JavaScriptCore/runtime/JSValue.h"

#include "statistics/statsstorage.h"
#include <iostream>

#include "domsnapshot.h"

namespace WebCore {

DOMSnapshotNodeImpl::DOMSnapshotNodeImpl(std::string elementAsString, Element* element)
    : DOMSnapshotNode()
{
    // xpath

    m_xpath = element->getXPath();

    // tagName (defined in element.idl)

    m_attributes.insert(std::pair<std::string, std::string>("tagName", element->tagName().ascii().data()));

    // nodeType (defined in node.idl)

    std::stringstream nodeType;
    nodeType << (unsigned)element->toNode()->nodeType();
    m_attributes.insert(std::pair<std::string, std::string>("nodeType", nodeType.str()));

    // DOM attributes, e.g. id and class. All attributes can be accessed through getAttribute.

    if (element->hasAttributes()) {
        for (size_t i = 0; i < element->attributeData()->length(); ++i) {
             Attribute* a = element->attributeData()->attributeItem(i);
             m_attributes.insert(std::pair<std::string, std::string>(
                                     a->name().toString().ascii().data(),
                                     a->value().string().ascii().data()));
        }
    }

    // toString representation
    m_attributes.insert(std::pair<std::string, std::string>("TOSTRING", elementAsString));
}

DOMSnapshotImpl::DOMSnapshotImpl(std::queue<std::pair<Node*, std::string> > queue)
    : DOMSnapshot()
{
    while (!queue.empty()) {
        std::pair<Node*, std::string> item = queue.front();
        queue.pop();

        Node* cur = item.first;
        std::string className = item.second;

        Element* element = dynamic_cast<Element*>(cur);
        if (element) {
            m_nodes.insert(std::pair<Symbolic::DOMSnapshotNodeId, Symbolic::DOMSnapshotNode*>(
                               (Symbolic::DOMSnapshotNodeId)cur, new DOMSnapshotNodeImpl(className, element)));
        }
    }
}

}

