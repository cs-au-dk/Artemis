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

#include "domsnapshotstorage.h"

namespace artemis
{


DomSnapshotStorage::DomSnapshotStorage()
{
}

bool DomSnapshotStorage::contains(QString key) const
{
    return mSnapshots.contains(key);
}

bool DomSnapshotStorage::contains(std::string key) const
{
    return contains(QString::fromStdString(key));
}

WebCore::DOMSnapshot DomSnapshotStorage::get(QString key) const
{
    assert(mSnapshots.contains(key));
    return mSnapshots.value(key);
}

WebCore::DOMSnapshot DomSnapshotStorage::get(std::string key) const
{
    return get(QString::fromStdString(key));
}



void DomSnapshotStorage::insert(QString key, WebCore::DOMSnapshot snapshot)
{
    mSnapshots.insert(key, snapshot);
}

void DomSnapshotStorage::create(QString key, BaseInput* input)
{
    // TODO: Create a snapshot from the DOM nodes relevant to the given ClickInput or DomInput.
}




QDebug operator<<(QDebug dbg, const DomSnapshotStorage &snapshots)
 {
    if (snapshots.mSnapshots.empty()) {
        dbg.nospace() << "<Empty snaphot storage>";
        return dbg.maybeSpace();
    }

    foreach (QString key, snapshots.mSnapshots.keys()) {
        dbg.nospace() << "Snapshot for " << key;

        WebCore::DOMSnapshot snap = snapshots.get(key);

        std::map<WebCore::DOMSnapshotNodeId, WebCore::DOMSnapshotNode*>::iterator nodeIter;
        for (nodeIter = snap.getNodes().begin(); nodeIter != snap.getNodes().end(); ++nodeIter) {

            dbg.nospace() << "  " << nodeIter->first << " => " << QString::fromStdString(nodeIter->second->getXpath());

        }
    }

     return dbg.maybeSpace();
 }


} // namespace artemis
