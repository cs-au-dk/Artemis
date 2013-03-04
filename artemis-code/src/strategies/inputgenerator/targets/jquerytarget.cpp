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

#include <QWebElement>
#include <QList>

#include "runtime/input/events/eventhandlerdescriptor.h"
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

QString JQueryTarget::getSignature(QWebElement element) const
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

QWebElement JQueryTarget::get(ArtemisWebPagePtr page) const
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
