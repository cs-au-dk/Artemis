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

#ifndef DOMSNAPSHOTSTORAGE_H
#define DOMSNAPSHOTSTORAGE_H

#include <QMap>
#include <QString>
#include <assert.h>

#include "WebCore/dom/domsnapshot.h"
#include "runtime/input/baseinput.h"

namespace artemis
{


class DomSnapshotStorage
{
    friend QDebug operator<<(QDebug dbg, const DomSnapshotStorage &snapshots);

public:
    DomSnapshotStorage();

    bool contains(QString key) const;
    bool contains(std::string key) const;

    WebCore::DOMSnapshot get(QString key) const;
    WebCore::DOMSnapshot get(std::string key) const;

    void insert(QString key, WebCore::DOMSnapshot snapshot);
    void create(QString key, BaseInput* input);

protected:
    QMap<QString, WebCore::DOMSnapshot> mSnapshots;
};


QDebug operator<<(QDebug dbg, const DomSnapshotStorage &snapshots);


} // namespace artemis
#endif // DOMSNAPSHOTSTORAGE_H
