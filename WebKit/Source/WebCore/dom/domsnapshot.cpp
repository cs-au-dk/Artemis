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

#include "statistics/statsstorage.h"
#include <iostream>

#include "domsnapshot.h"

namespace WebCore {

DOMSnapshotNodeImpl::DOMSnapshotNodeImpl(Element* element)
    : DOMSnapshotNode()
{
    // xpath

    m_xpath = "TODO";

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

    // TODO
    //m_attributes.insert(std::pair<std::string, std::string>("class", element->getAttribute(WTF::String("class")).string().ascii().data()));
}

DOMSnapshotImpl::DOMSnapshotImpl(Node* base)
    : DOMSnapshot()
{
    std::queue<Node*> queue;
    queue.push(base);

    // add all relevant child elements
    WTF::RefPtr<NodeList> l = WTF::getPtr(base->getElementsByTagName(WTF::AtomicString("*")));
    for (unsigned i = 0; i < l->length(); ++i) {
        queue.push(l->item(i));
    }

    while (!queue.empty()) {
        Node* cur = queue.front();
        queue.pop();

        Element* element = dynamic_cast<Element*>(cur);
        if (element) {
            m_nodes.insert(std::pair<Symbolic::DOMSnapshotNodeId, Symbolic::DOMSnapshotNode*>(
                               (Symbolic::DOMSnapshotNodeId)cur, new DOMSnapshotNodeImpl(element)));
        }
    }
}

}

