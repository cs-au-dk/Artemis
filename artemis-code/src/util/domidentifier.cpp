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
/*
#include "domidentifier.h"

namespace artemis
{

uint DomIdentifier::getIdentifier(JSC::JSObject* object, JSC::ExecState* exec)
{
    // If there is no 'artemis-dom-identifier' property present, then set one.

    // The name of the property, confusingly for this method called the Identifier.
    JSC::Identifier name(exec, "artemis-dom-identifier");

    if (object->hasOwnProperty(exec, name)) {
        // Fetch an existing property from the object.
        JSC::JSValue id = object->get(exec, name);

        assert(id.isUInt32());
        return id.asUInt32();

    } else {
        // Add a new property to the object.
        mIdCounter++;
        JSC::JSValue newId(mIdCounter);
        object->putDirect(exec->globalData(), name, newId);

        // Sanity check as I don't understand the JSObject API fully.
        JSC::JSValue readId = object->get(exec, name);
        assert(readId.isUInt32());
        assert(readId.asUInt32() == mIdCounter);

        return mIdCounter;
    }
}




} // namespace artemis */
