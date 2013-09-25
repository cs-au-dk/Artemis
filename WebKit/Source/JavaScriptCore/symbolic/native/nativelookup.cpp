/*
 * Copyright 2012 Aarhus University
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

#ifdef ARTEMIS

#include <utility>
#include <iostream>

#include "WTF/wtf/ExportMacros.h"
#include "config.h"
#include "JavaScriptCore/bytecode/CodeBlock.h"
#include "JavaScriptCore/interpreter/CallFrame.h"

#include "natives.h"

#include "nativelookup.h"

namespace Symbolic
{

NativeLookup::NativeLookup()
{
    /*
     * m_nativeFunctionMap.insert(std::make_pair<JSC::native_function_ID_t, NativeFunction>(nativeFunctionID, NativeFunction(path)));
     */

}

const NativeFunction* NativeLookup::find(JSC::native_function_ID_t functionID)
{
    function_map_t::iterator iter = m_nativeFunctionMap.find(functionID);
    if (iter != m_nativeFunctionMap.end()) {
        return &iter->second;
    } else {
        return NULL;
    }
}

}

#endif
