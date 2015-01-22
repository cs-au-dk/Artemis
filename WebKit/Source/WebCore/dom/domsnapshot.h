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

#ifndef DOMSNAPSHOT_H
#define DOMSNAPSHOT_H

#include <list>
#include <map>
#include <string>
#include <queue>


namespace WebCore {

class Node;
class Element;

/**
 *  Note: The interfaces and implementations here (e.g. DOMSnapshot and DOMSnapshotImpl are separate because they used to be defined in different places.
 */

typedef long DOMSnapshotNodeId;
typedef std::map<std::string, std::string> DOMSnapshotNodeAttributes;

class DOMSnapshotNode
{

public:
    DOMSnapshotNode() {}

    std::string getXpath() {
        return m_xpath;
    }

    const DOMSnapshotNodeAttributes getAttributes() {
        return m_attributes;
    }

protected:
    std::string m_xpath;
    DOMSnapshotNodeAttributes m_attributes;

};

class DOMSnapshot
{
public:
    DOMSnapshot() {}

    ~DOMSnapshot() {

        std::map<DOMSnapshotNodeId, DOMSnapshotNode*>::iterator iter;
        for (iter = m_nodes.begin(); iter != m_nodes.end(); ++iter) {
            delete iter->second;
        }

    }

    inline std::map<DOMSnapshotNodeId, DOMSnapshotNode*> getNodes() {
        return m_nodes;
    }

protected:
    std::map<DOMSnapshotNodeId, DOMSnapshotNode*> m_nodes;
};



class DOMSnapshotNodeImpl : public DOMSnapshotNode
{

public:
    DOMSnapshotNodeImpl(std::string elementAsString, WebCore::Element* element);
};

class DOMSnapshotImpl : public DOMSnapshot
{
public:
    DOMSnapshotImpl(std::queue<std::pair<unsigned, std::pair<Element*, std::string> > > queue);
};

}

#endif // DOMSNAPSHOT_H
