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

#include "eventypes.h"
#include "util/randomutil.h"
#include "artemisglobals.h"

#include "baseeventparameters.h"

namespace artemis
{

BaseEventParameters::BaseEventParameters(QString name, bool bubbles, bool cancelable) :
    EventParameters(),
    name(name),
    cancelable(cancelable),
    bubbles(bubbles)

{
    Q_ASSERT(!name.isEmpty());
}

QString BaseEventParameters::getJsString() const
{
    if (!cachedJsString.isEmpty()) {
        return cachedJsString;
    }

    QString randId = generateRandomJsId();
    QString res = "var " + randId + " = document.createEvent(\"Event\");";
    res = res + " " + randId + ".initEvent(";
    res += quoteString(name) = ",";
    res += boolTostring(bubbles) + ",";
    res += boolTostring(cancelable) + ",);";

    res += "this.dispatchEvent(" + randId + ");";

    cachedJsString = res;
    return res;
}

EventType BaseEventParameters::getType() const
{
    return BASE_EVENT;
}

}
