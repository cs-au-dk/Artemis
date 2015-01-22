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

#include "runtime/input/dominput.h"

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

WebCore::DOMSnapshot* DomSnapshotStorage::get(QString key) const
{
    assert(mSnapshots.contains(key));
    return mSnapshots.value(key);
}

WebCore::DOMSnapshot* DomSnapshotStorage::get(std::string key) const
{
    return get(QString::fromStdString(key));
}



void DomSnapshotStorage::insert(QString key, WebCore::DOMSnapshot* snapshot)
{
    mSnapshots.insert(key, snapshot);
}

void DomSnapshotStorage::create(QSharedPointer<const BaseInput> input, ArtemisWebPagePtr page, unsigned symbolicSessionId)
{
    // Create a snapshot from the DOM nodes relevant to the given DomInput.
    // TODO: Also support ClickInput in a similar way.

    QSharedPointer<const DomInput> domInput = input.dynamicCast<const DomInput>();

    if (!domInput) {
        return;
    }

    QString jsToGetArtemisId = "this[\"artemisId\"]";
    QString jsToGetStringRepr = "this.toString()";

    QWebElement targetQWebElement = domInput->getTarget()->get(page);
    WebCore::Element* targetElement = targetQWebElement.getElement();

    QString artemisVariableName = QString("SYM_TARGET_%1").arg(symbolicSessionId); // Must match the name generated in CodeGeneratorJS.pm in the section on SymbolicEventTarget.

    QVariant targetIdFromDom = targetQWebElement.evaluateJavaScript(jsToGetArtemisId);
    assert(targetIdFromDom.canConvert(QVariant::UInt));
    unsigned targetId = targetIdFromDom.toUInt();

    QString targetStringRepr = targetQWebElement.evaluateJavaScript(jsToGetStringRepr).toString();

    // Note, the third parameter is the "to string" version of the object, which we need for certain constraints.
    std::queue<std::pair<unsigned, std::pair<WebCore::Element*, std::string> > > queue;

    // Insert the top-level target element into the snapshot.
    queue.push(std::pair<unsigned, std::pair<WebCore::Element*, std::string> >(targetId, std::pair<WebCore::Element*, std::string>(targetElement, targetStringRepr.toStdString())));

    // The snapshot consists of all elements in the subtree of the target of the event.
    QWebElementCollection children = targetQWebElement.findAll("*");
    foreach (QWebElement element, children) {
        WebCore::Element* elementPtr = element.getElement();

        QVariant elementIdFromDom = element.evaluateJavaScript(jsToGetArtemisId);
        assert(elementIdFromDom.canConvert(QVariant::UInt));
        unsigned elementId = elementIdFromDom.toUInt();

        QString elementStringRepr = element.evaluateJavaScript(jsToGetStringRepr).toString();

        queue.push(std::pair<unsigned, std::pair<WebCore::Element*, std::string> >(elementId, std::pair<WebCore::Element*, std::string>(elementPtr, elementStringRepr.toStdString())));
    }

    // Build a snapshot from the list of node info.
    WebCore::DOMSnapshot* domSnapshot = new WebCore::DOMSnapshotImpl(queue);
    insert(artemisVariableName, domSnapshot);
}

void DomSnapshotStorage::reset()
{
    mSnapshots.clear();
}




QDebug operator<<(QDebug dbg, const DomSnapshotStorage &snapshots)
 {
    if (snapshots.mSnapshots.empty()) {
        dbg.nospace() << "<Empty snaphot storage>";
        return dbg.maybeSpace();
    }

    foreach (QString key, snapshots.mSnapshots.keys()) {
        dbg.nospace() << "Snapshot for " << key;

        WebCore::DOMSnapshot* snap = snapshots.get(key);

        std::map<WebCore::DOMSnapshotNodeId, WebCore::DOMSnapshotNode*>::iterator nodeIter;
        for (nodeIter = snap->getNodes().begin(); nodeIter != snap->getNodes().end(); ++nodeIter) {

            dbg.nospace() << "  " << nodeIter->first << " => " << QString::fromStdString(nodeIter->second->getXpath());

        }
    }

     return dbg.maybeSpace();
 }


} // namespace artemis
