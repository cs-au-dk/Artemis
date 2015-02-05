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

#ifndef FIELDREADLOG_H
#define FIELDREADLOG_H

#include <QString>
#include <QPair>
#include <QVariant>

#include "runtime/browser/artemiswebpage.h"

namespace artemis
{

/**
 * Keeps a record of symbolic fields which are read during different events.
 * This is similar to HandlerDependencyTracker but with a different focus.
 */
class FieldReadLog : public QObject
{
    Q_OBJECT

public:
    FieldReadLog(ArtemisWebPagePtr page);

    typedef QPair<QString, QString> Event;
    typedef QString Field;

    void beginEvent(QString eventType, QString elementXPath);
    void clear();
    QVariantList getLog();

public slots:
    void slJavascriptSymbolicFieldRead(QString variable, bool isSymbolic);

protected:
    ArtemisWebPagePtr mPage; // Used to look up the XPaths of fields.

    Event mCurrentEvent;

    QMap<QPair<Event, Field>, uint> mFieldsRead;
    QMap<Field, QString> mFieldXPaths;

    QString lookupXPath(QString variable);
    void logFieldRead(Event event, Field field);
};

} // namespace artemis
#endif // FIELDREADLOG_H
