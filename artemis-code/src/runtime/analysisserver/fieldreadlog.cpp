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

#include <QWebFrame>
#include <QWebElement>

#include "util/loggingutil.h"

#include "fieldreadlog.h"

namespace artemis
{

FieldReadLog::FieldReadLog(ArtemisWebPagePtr page)
    : mPage(page)
    , mCurrentEvent("[none]", "")
{
}

void FieldReadLog::beginEvent(QString eventType, QString elementXPath)
{
    mCurrentEvent = Event(eventType, elementXPath);
}

void FieldReadLog::slJavascriptSymbolicFieldRead(QString variable, bool isSymbolic)
{
    variable.remove(QRegExp("^SYM_IN_(INT_|BOOL_)?"));

    if (!mFieldXPaths.contains(variable)) {
        mFieldXPaths.insert(variable, lookupXPath(variable));
    }

    logFieldRead(mCurrentEvent, variable);
}

QString FieldReadLog::lookupXPath(QString variable)
{
    // Variable names are also IDs in the DOM.
    QWebElement element = mPage->mainFrame()->findFirstElement(QString("#%1").arg(variable));
    if (element.isNull()) {
        Log::warning(QString("Warning: Could not find field %1 in FieldReadLog").arg(variable).toStdString());
        return QString();
    }
    return element.xPath();
}

void FieldReadLog::logFieldRead(Event event, Field field)
{
    QPair<Event, Field> read(event, field);
    uint count = 1;
    if (mFieldsRead.contains(read)) {
        count = mFieldsRead.value(read) + 1;
    }
    mFieldsRead.insert(read, count);
}

void FieldReadLog::clear()
{
    mCurrentEvent = QPair<QString, QString>("[none]", "");
    mFieldsRead.clear();
    mFieldXPaths.clear();
}

QVariantList FieldReadLog::getLog()
{
    // Structure of the returned log is a list of event log objects of the following format:
    // { "event": "click", "element": "//a[@id='someButton']", "reads": [ ... ] }
    // Each read object looks like this:
    // { "field": "//input[@id='myField']", "count": 7 }
    // We merge mFieldsRead and mFieldXPaths to build this, as the internal variable names are not interesting in the server mode API.

    QMap<Event, QList<QVariant> > reads;

    typedef QPair<Event, Field> Read;
    foreach (Read read, mFieldsRead.keys()) {
        QVariantMap readObj;
        readObj.insert("field", mFieldXPaths.value(read.second));
        readObj.insert("count", mFieldsRead.value(read));

        // operator[] returns a reference to a default empty list if this Event is not yet in the map.
        reads[read.first].append(readObj);
    }

    QVariantList result;

    foreach (Event evt, reads.keys()) {
        QVariantMap evtObj;
        evtObj.insert("event", evt.first);
        evtObj.insert("element", evt.second);
        evtObj.insert("reads", reads.value(evt));

        result.append(evtObj);
    }

    return result;
}


} // namespace artemis
