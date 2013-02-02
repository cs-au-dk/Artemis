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

#include <QWebElement>
#include <QList>

#include "runtime/events/eventhandlerdescriptor.h"
#include "strategies/inputgenerator/targets/jquerylistener.h"
#include "util/randomutil.h"

#include "jquerytarget.h"

namespace artemis
{

JQueryTarget::JQueryTarget(QObject* parent,
                           const EventHandlerDescriptor* eventHandler,
                           JQueryListener* jqueryListener) :
    TargetDescriptor(parent, eventHandler)
{
    mJQueryListener = jqueryListener;
    mJQueryListener->setParent(this);
}

QString JQueryTarget::getSignature(QWebElement element)
{
    if (element.isNull()) {
        return QString("");
    }

    QString result = getSignature(element.parent());

    if (element.tagName() == QString("HTML")) {
        result = result.append("#document.HTML");
    }
    else {
        result = result.append(element.tagName());
    }

    result = result.append(QString("."));

    return result;
}

QWebElement JQueryTarget::get(ArtemisWebPage* page)
{
    QWebElement element = mEventHandler->domElement()->getElement(page);

    if (element.isNull()) {
        return QWebElement();
    }

    QString signature = getSignature(element);
    QString event = mEventHandler->name();

    qDebug() << "TARGET::Info, looking for selectors for signature " << signature << " and event " << event << endl;

    QList<QString> selectors = mJQueryListener->lookup(signature, event);

    if (selectors.count() == 0) {
        qDebug() << "TARGET::Warning, no matching selectors found, defaulting to source" << endl;
        return element;
    }

    /* Select random selector */
    QString selector = pickRand(selectors);

    /* Select target element */
    //QWebElementCollection elements = page->currentFrame()->findAllElements(selector);
    QWebElementCollection elements = element.findAll(selector);

    if (elements.count() == 0) {
        qDebug() << "TARGET::Warning, no matching elements found, defaulting to source" << endl;
        return element;

    }
    else {
        QWebElement element = pickRand(elements.toList());

        QString name = element.tagName();
        qDebug() << "TARGET::Selecting element " << name << " out of a total of " << elements.count() << "element(s) and " << selectors.count() << " selector(s)" << endl;

        return element;
    }
}
}
