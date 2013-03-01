/*
 * Copyright 2012 Aarhus University
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <QDebug>
#include <QStringList>

#include "jquerylistener.h"

using namespace std;

namespace artemis
{

JQueryListener::JQueryListener(QObject* parent) : QObject(parent)
{

}

void JQueryListener::reset()
{
    jqueryEvent* event;
    foreach(event, jqueryEvents) {
        delete event;
    }

    jqueryEvents.clear();
}

QList<QString> JQueryListener::lookup(QString elementSignature, QString event)
{
    QList<QString> result;

    jqueryEvent* e;
    foreach(e, jqueryEvents) {

        if (e->event == event) {

            qDebug() << "Comparing " << elementSignature << " with " << e->elementSignature << endl;

            // The following adds support for fuzzy matching. If an event handler
            // is added at runtime to an element, which are not yet linked to the
            // dom tree, then its "root" is called #document-fragment... Thus we
            // can't get a full signature. These "signatures" are matched using
            // best effort principles
            if (e->elementSignature.indexOf(QString("#document-fragment")) != -1) {
                QString trimmed = QString(e->elementSignature).replace(QString("#document-fragment"), QString(""));

                if (elementSignature.indexOf(trimmed) != -1) {
                    qDebug() << "Found match (fuzzy)" << endl;
                    result.append(e->selector);
                }
            }

            else if (e->elementSignature == elementSignature) {
                result.append(e->selector);
                qDebug() << "Found match" << endl;
            }

        }
    }

    return result;
}

void JQueryListener::slEventAdded(QString elementSignature, QString event, QString selector)
{
    jqueryEvent* e = new jqueryEvent();
    e->elementSignature = elementSignature;
    e->selector = selector;

    /* Jquery supports namespaced events, e.g. we can bind to the event
     * click.something, where click is the event and something is a namespace.
     * This is used to only access a subset of registered listeres, e.g.
     * only triggering or removing "something" listeners.
     * In this case, we remove information regarding namespaces and handle all
     * events equally. This should not be a problem since we are only interested
     * in triggering all events from the user's/browser's point of view.
     */
    QStringList parts = event.split(QString("."));
    e->event = parts[0];

    jqueryEvents.append(e);
    qDebug() << "Jquery::Eventhandler registered for event " << event << " and selector " << selector << " on dom node with signature " << elementSignature << endl;
}

}
