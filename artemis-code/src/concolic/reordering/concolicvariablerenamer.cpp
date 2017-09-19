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

#include "concolicvariablerenamer.h"

#include <assert.h>
#include "util/loggingutil.h"

namespace artemis
{

ConcolicVariableRenamer::ConcolicVariableRenamer(QStringList variables, uint pcIndex)
{
    mIndex = pcIndex; // Really this is meaningless until setIndex or setPcIndex has been called.
    mPcIndex = pcIndex;
    mVariablesToRename = variables;
}

void ConcolicVariableRenamer::setIndex(uint index)
{
    mIndex = index;
}

void ConcolicVariableRenamer::setPcIndex()
{
    mIndex = mPcIndex;
}

QString ConcolicVariableRenamer::encode(QString name)
{
    // Only rename the variables which we know to be associated with the actions we're analysing.
    if (mVariablesToRename.contains(name)) {
        QString result = QString("%1__%2").arg(name).arg(mIndex);
        Log::debug("ConcolicVariableRenamer: Encoding " + name.toStdString() + " to " + result.toStdString());
        assert(!mVariablesToRename.contains(result)); // Sanity check, not strictly impossible.
        mEncodedVars[result] = name;
        return result;
    } else {
        Log::debug("ConcolicVariableRenamer: Not encoding " + name.toStdString());
        return name;
    }
}

QString ConcolicVariableRenamer::decode(QString name)
{
    if (mEncodedVars.contains(name)) {
        Log::debug("ConcolicVariableRenamer: Decoding " + name.toStdString() + " to " + mEncodedVars[name].toStdString());
        return mEncodedVars[name];
    } else {
        Log::debug("ConcolicVariableRenamer: Not decoding " + name.toStdString());
        return name;
    }
}

} // namespace artemis
