/*
  Copyright 2011 Simon Holm Jensen. All rights reserved.

  Redistribution and use in source and binary forms, with or without modification, are
  permitted provided that the following conditions are met:

     1. Redistributions of source code must retain the above copyright notice, this list of
        conditions and the following disclaimer.

     2. Redistributions in binary form must reproduce the above copyright notice, this list
        of conditions and the following disclaimer in the documentation and/or other materials
        provided with the distribution.

  THIS SOFTWARE IS PROVIDED BY SIMON HOLM JENSEN ``AS IS'' AND ANY EXPRESS OR IMPLIED
  WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND
  FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL <COPYRIGHT HOLDER> OR
  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
  CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
  SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
  ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
  NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
  ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

  The views and conclusions contained in the software and documentation are those of the
  authors and should not be interpreted as representing official policies, either expressed
  or implied, of Simon Holm Jensen
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
