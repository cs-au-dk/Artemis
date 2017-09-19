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

#ifndef CONCOLICVARIABLERENAMER_H
#define CONCOLICVARIABLERENAMER_H

#include <QSharedPointer>
#include <QString>
#include <QPair>
#include <QStringList>
#include <QMap>

namespace artemis
{

class ConcolicVariableRenamer
{
public:
    ConcolicVariableRenamer(QStringList variables, uint pcIndex);

    void setIndex(uint index);
    void setPcIndex(); // Sets the current index to that of the currently-analysed action.

    QString encode(QString name);
    QString decode(QString name);

protected:
    QStringList mVariablesToRename;
    uint mIndex;
    uint mPcIndex;
    QMap<QString, QString> mEncodedVars;
};
typedef QSharedPointer<ConcolicVariableRenamer> ConcolicVariableRenamerPtr;

} // namespace artemis
#endif // CONCOLICVARIABLERENAMER_H
