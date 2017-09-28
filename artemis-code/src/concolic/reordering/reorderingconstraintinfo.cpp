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

#include "reorderingconstraintinfo.h"

#include <assert.h>
#include "util/loggingutil.h"

namespace artemis
{

ReorderingConstraintInfo::ReorderingConstraintInfo(QMap<uint, QPair<QString, InjectionValue> > actionVariables, QMap<uint, QPair<QString, InjectionValue> > actionIndexVariables, uint pcIndex, uint submitButtonIndex)
{
    mIndex = pcIndex; // Really this is meaningless until setIndex or setPcIndex has been called.
    mPcIndex = pcIndex;
    mSubmitButtonIndex = submitButtonIndex;
    mActionVariables = actionVariables;
    mActionIndexVariables = actionIndexVariables;
    mVariablesToRename = QStringList();
    foreach (ActionInfo actionInfo, mActionVariables.values()) {
        mVariablesToRename.append(actionInfo.first);
    }
    foreach (ActionInfo actionInfo, mActionIndexVariables.values()) {
        mVariablesToRename.append(actionInfo.first);
    }
}

void ReorderingConstraintInfo::setIndex(uint index)
{
    mIndex = index;
}

void ReorderingConstraintInfo::setPcIndex()
{
    mIndex = mPcIndex;
}

QString ReorderingConstraintInfo::encode(QString name)
{
    // Only rename the variables which we know to be associated with the actions we're analysing.
    if (mVariablesToRename.contains(name)) {
        QString result = encodeWithExplicitIndex(name, mIndex);
        //Log::debug("ReorderingConstraintInfo: Encoding " + name.toStdString() + " to " + result.toStdString());
        assert(!mVariablesToRename.contains(result)); // Sanity check, not strictly impossible.
        mEncodedVars[result] = name;
        return result;
    } else {
        //Log::debug("ReorderingConstraintInfo: Not encoding " + name.toStdString());
        return name;
    }
}

QString ReorderingConstraintInfo::encodeWithExplicitIndex(QString name, uint index)
{
    // N.B. This method does not include the sanity checking. It's just here to guarantee that other parts of the code
    // that try to match the encoding can use the same method.
    return QString("%1__%2").arg(name).arg(index);
}

QString ReorderingConstraintInfo::decode(QString name)
{
    if (mEncodedVars.contains(name)) {
        //Log::debug("ReorderingConstraintInfo: Decoding " + name.toStdString() + " to " + mEncodedVars[name].toStdString());
        return mEncodedVars[name];
    } else {
        //Log::debug("ReorderingConstraintInfo: Not decoding " + name.toStdString());
        return name;
    }
}

QMap<uint, QPair<QString, InjectionValue> > ReorderingConstraintInfo::getActionVariables()
{
    return mActionVariables;
}

QMap<uint, QPair<QString, InjectionValue> > ReorderingConstraintInfo::getActionIndexVariables()
{
    return mActionIndexVariables;
}

uint ReorderingConstraintInfo::getSubmitButtonIndex()
{
    return mSubmitButtonIndex;
}

} // namespace artemis
