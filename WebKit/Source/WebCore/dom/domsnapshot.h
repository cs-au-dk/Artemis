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

#include "JavaScriptCore/symbolic/expression/symbolicsource.h"

namespace WebCore {

class Node;
class Element;

class DOMSnapshotNodeImpl : public Symbolic::DOMSnapshotNode
{

public:
    DOMSnapshotNodeImpl(std::string elementAsString, WebCore::Element* element);
};

class DOMSnapshotImpl : public Symbolic::DOMSnapshot
{
public:
    DOMSnapshotImpl(std::queue<std::pair<unsigned, std::pair<Node*, std::string> > > queue);
};

}

#endif // DOMSNAPSHOT_H
