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

#ifndef REORDERINGCONSTRAINTINFO_H
#define REORDERINGCONSTRAINTINFO_H

#include <QSharedPointer>
#include <QString>
#include <QMap>
#include <QMultiMap>
#include <QPair>
#include <QStringList>

#include "runtime/input/forms/injectionvalue.h"

namespace artemis
{

class ReorderingConstraintInfo
{
public:
    ReorderingConstraintInfo(QMultiMap<uint, QPair<QString, InjectionValue>> actionVariables, uint pcIndex);

    void setIndex(uint index);
    void setPcIndex(); // Sets the current index to that of the currently-analysed action.

    QString encode(QString name);
    static QString encodeWithExplicitIndex(QString name, uint index);
    QString decode(QString name);

    QMultiMap<uint, QPair<QString, InjectionValue>> getActionVariables();

protected:
    QMultiMap<uint, QPair<QString, InjectionValue>> mActionVariables;
    QStringList mVariablesToRename;
    uint mIndex;
    uint mPcIndex;
    QMap<QString, QString> mEncodedVars;
};
typedef QSharedPointer<ReorderingConstraintInfo> ReorderingConstraintInfoPtr;
typedef QPair<QString, InjectionValue> ActionInfo;

} // namespace artemis
#endif // REORDERINGCONSTRAINTINFO_H
