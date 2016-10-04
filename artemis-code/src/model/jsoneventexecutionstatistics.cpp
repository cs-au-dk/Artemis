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

#include "util/fileutil.h"
#include "runtime/input/events/keyboardeventparameters.h"
#include "runtime/input/events/mouseeventparameters.h"
#include "runtime/input/events/baseeventparameters.h"
#include <QDateTime>

#include "jsoneventexecutionstatistics.h"

namespace artemis {

JSONEventExecutionStatistics::JSONEventExecutionStatistics(const QUrl& url){
    mUrl = url;
    init = false;
}

void JSONEventExecutionStatistics::registerEvent(EventTuple desc){
    mCurrentRegisteredHandlers.append(desc);
}

void JSONEventExecutionStatistics::beginNewIteration(){
    if(init){
        mRegisteredHandlers.append(mCurrentRegisteredHandlers);
    }
    init = true;
    mCurrentRegisteredHandlers = QList<EventTuple>();
}


void JSONEventExecutionStatistics::generateOutput(){
    beginNewIteration();

    QString out = QString("{\"url\":\"").append(mUrl.toString()).
            append("\","
                   "\"iterations\": [");
    bool first = true;
    foreach(QList<EventTuple> list, mRegisteredHandlers){
        if(!first){
            out.append(", ");
        }


        out.append("[");
        bool first2 = true;
        foreach(EventTuple desc, list){

            if(!first2){
                out.append(", ");
            }
            out.append(eventTupleToJSONString(desc));
            first2 = false;
        }
        out.append("]");

        first = false;

    }

    out.append("]}");
    QString timeString = QDateTime::currentDateTime().toString("dd-MM-yy-hh-mm-ss");
    QString fileName = QString("json-event-execution-").append(timeString).append(".json");

    writeStringToFile(fileName, out);
}

QString JSONEventExecutionStatistics::eventTupleToJSONString(EventTuple evt){
    QSharedPointer<const MouseEventParameters> mep = qSharedPointerDynamicCast<const MouseEventParameters>(evt.mEvtParams);
    QSharedPointer<const KeyboardEventParameters> kep = qSharedPointerDynamicCast<const KeyboardEventParameters>(evt.mEvtParams);
    QSharedPointer<const BaseEventParameters> bep = qSharedPointerDynamicCast<const BaseEventParameters>(evt.mEvtParams);

    QString out = "{";
    out.append("\"name\":\"").append(QString(evt.mEventHandler->getName()).replace("\"", "\\\"")).append("\"");
    if(mep){

        out.append(", \"canBubble\":").append(mep->canBubble?"true":"false");
        out.append(", \"cancelable\":").append(mep->cancelable?"true":"false");
        out.append(", \"ctrlKey\":").append(mep->ctrlKey?"true":"false");
        out.append(", \"altKey\":").append(mep->altKey?"true":"false");
        out.append(", \"shiftKey\":").append(mep->shiftKey?"true":"false");
        out.append(", \"metaKey\":").append(mep->metaKey?"true":"false");
        out.append(", \"typeN\":\"").append(QString(mep->typeN).replace("\"", "\\\"")).append("\"");
        out.append(", \"screenX\":").append(QString::number(mep->screenX));
        out.append(", \"screenY\":").append(QString::number(mep->screenY));
        out.append(", \"clientX\":").append(QString::number(mep->clientX));
        out.append(", \"clientY\":").append(QString::number(mep->clientY));
        out.append(", \"button\":").append(QString::number(mep->button));

    } else if(kep){

        out.append(", \"canBubble\":").append(kep->canBubble?"true":"false");
        out.append(", \"cancelable\":").append(kep->cancelable?"true":"false");
        out.append(", \"ctrlKey\":").append(kep->ctrlKey?"true":"false");
        out.append(", \"altKey\":").append(kep->altKey?"true":"false");
        out.append(", \"shiftKey\":").append(kep->shiftKey?"true":"false");
        out.append(", \"metaKey\":").append(kep->metaKey?"true":"false");
        out.append(", \"altGraphKey\":").append(kep->altGraphKey?"true":"false");
        out.append(", \"keyIdentifier\":\"").append(QString(kep->keyIdentifier).replace("\"", "\\\"")).append("\"");
        out.append(", \"eventType\":\"").append(QString(kep->keyIdentifier).replace("\"", "\\\"")).append("\"");
        out.append(", \"keyLocation\":").append(QString::number(kep->keyLocation));

    }
    out.append(", \"formInput\": [").append(formInputToJSONString(evt.mFormInput)).append("]");

    return out.append(", \"targetXPath\": \"").append(QString(evt.mEventHandler->xPathToElement()).replace("\"", "\\\"")).append("\"").append("}");

}

QString JSONEventExecutionStatistics::formInputToJSONString(FormInputCollectionConstPtr formInput)
{
    QStringList items;
    foreach (FormInputPair fip, formInput->getInputs()) {
        QString itemStr = "[\"";
        itemStr.append(fip.first->getDomElement()->getXPath().replace("\"", "\\\""));
        itemStr.append("\", \"");
        itemStr.append(fip.second.toString());
        itemStr.append("\"]");
        items.append(itemStr);
    }
    return items.join(", ");
}

} // namespace artemis
