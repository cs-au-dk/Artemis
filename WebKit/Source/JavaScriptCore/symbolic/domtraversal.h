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

#ifndef DOMTRAVERSAL_H
#define DOMTRAVERSAL_H

#ifdef ARTEMIS

#include <tr1/unordered_set>

namespace JSC {
    class ExecState;
    class JSObject;
    class JSValue;
}

namespace Symbolic
{

class DomTraversal
{

public:
    explicit DomTraversal() {}

    static void traverseDom(JSC::CallFrame* callFrame, DomTraversal* callback);

protected:
    virtual bool domNodeTraversalCallback(JSC::CallFrame* callFrame, std::string path, JSC::JSValue jsValue) = 0;

};

}

#endif
#endif // DOMTRAVERSAL_H
