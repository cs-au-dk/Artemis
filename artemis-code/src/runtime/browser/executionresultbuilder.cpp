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

#include <sstream>

#include <QWebFrame>

#include "statistics/statsstorage.h"
#include "util/loggingutil.h"

#include "executionresultbuilder.h"

namespace artemis
{

ExecutionResultBuilder::ExecutionResultBuilder(ArtemisWebPagePtr page) : QObject(NULL)
{
    mPage = page;
    reset();
}

void ExecutionResultBuilder::reset()
{
    mResult = QSharedPointer<ExecutionResult>(new ExecutionResult());
    mElementPointers.clear();
    mPageStateAfterLoad = QString("");
}

void ExecutionResultBuilder::notifyPageLoaded()
{
    mPageStateAfterLoad = mPage->mainFrame()->toHtml();
}

void ExecutionResultBuilder::notifyStartingEvent()
{
    mResult->mJavascriptConstantsObservedForLastEvent.clear();
}

void ExecutionResultBuilder::notifyStartingLoad()
{
    mResult->mJavascriptConstantsObservedForLastEvent.clear();
}

QSharedPointer<ExecutionResult> ExecutionResultBuilder::getResult()
{
    registerFromFieldsIntoResult();
    registerEventHandlersIntoResult();

    mResult->mPageContents = mPage->mainFrame()->toHtml();
    mResult->mStateHash = qHash(mResult->mPageContents);
    mResult->mModifiedDom = mResult->mPageContents.localeAwareCompare(mPageStateAfterLoad) != 0;

    return mResult;
}

void ExecutionResultBuilder::registerEventHandlersIntoResult()
{

    QPair<QWebElement*, QString> p;
    foreach(p, mElementPointers) {
        if (getType(p.second) == UNKNOWN_EVENT) {
            qWarning() << "Ignoring unsupported event of type " << p.second;
            continue;
        }

        if (p.first->isNull()) {
            qWarning() << "Got event handler with NULL element. Assuming document is reciever";
        }

        qDebug() << "Finalizing " << p.second << " xpath=" << p.first->xPath() << " _T: "
                 << p.first->attribute(QString("title"));
        EventHandlerDescriptorConstPtr handler = EventHandlerDescriptorConstPtr(new EventHandlerDescriptor(p.first, p.second));

        if (handler->isInvalid()) {
            qWarning() << "element was invalid, ignoring";
        } else {
            mResult->mEventHandlers.append(handler);
        }
    }

}

void ExecutionResultBuilder::registerFromFieldsIntoResult()
{
    mPage->updateFormIdentifiers(); // make sure that form identifiers (Artemis IDs) are set

    foreach(QWebFrame* frame, getAllFrames()) {
        // Gather <input> elements
        foreach(QWebElement input, frame->findAllElements("input")) {

            FormFieldTypes type =  getTypeFromAttr(input.attribute("type"));

            if (type == NO_INPUT) {
                continue;
            }

            DOMElementDescriptorConstPtr elementDescriptor = DOMElementDescriptorConstPtr(new DOMElementDescriptor(&input));
            FormFieldDescriptorPtr fieldDescriptor = FormFieldDescriptorPtr(new FormFieldDescriptor(type, elementDescriptor));

            mResult->mFormFields.insert(fieldDescriptor);
        }

        // Gather <textarea> elements
        foreach(QWebElement ta, frame->findAllElements("textarea")) {

            FormFieldDescriptorPtr taf = FormFieldDescriptorPtr(new FormFieldDescriptor(TEXT, DOMElementDescriptorConstPtr(new DOMElementDescriptor(&ta))));
            mResult->mFormFields.insert(taf);
        }

        // Gather select tags
        foreach(QWebElement ss, frame->findAllElements("select")) {
            QSet<QString> options = getSelectOptions(ss);
            FormFieldDescriptorPtr ssf = FormFieldDescriptorPtr(new FormFieldDescriptor(FIXED_INPUT, DOMElementDescriptorConstPtr(new DOMElementDescriptor(&ss)), options));
            mResult->mFormFields.insert(ssf);
        }
    }
}

QSet<QWebFrame*> ExecutionResultBuilder::getAllFrames()
{
    QSet<QWebFrame*> res;
    QWebFrame* main = mPage->mainFrame();
    res.insert(main);
    QList<QWebFrame*> worklist;
    worklist.append(main);

    while (!worklist.isEmpty()) {
        QWebFrame* c = worklist.takeFirst();
        worklist += c->childFrames();
        res += c->childFrames().toSet();
    }

    return res;
}

QSet<QString> ExecutionResultBuilder::getSelectOptions(const QWebElement& e)
{
    QSet<QString> res;
    QWebElementCollection options = e.findAll("option");
    foreach(QWebElement o, options) {
        QString valueAttr = o.attribute("value");

        if (!valueAttr.isEmpty())
            { valueAttr = o.toPlainText(); }

        if (valueAttr.isEmpty()) {
            Log::warning("Found empty option element in select, ignoring");
            continue;
        }

        res << valueAttr;
    }
    return res;
}

/** LISTENERS **/

void ExecutionResultBuilder::slEventListenerAdded(QWebElement* elem, QString eventName)
{
    Q_CHECK_PTR(elem);

    qDebug() << "Detected EVENTHANDLER event =" << eventName
             << "tag =" << elem->tagName()
             << "id =" << elem->attribute(QString("id"))
             << "title =" << elem->attribute(QString("title"))
             << "class =" << elem->attribute("class");

    if (isNonInteractive(eventName)) {
        return;
    }

    mElementPointers.append(QPair<QWebElement*, QString>(elem, eventName));
}

void ExecutionResultBuilder::slEventListenerRemoved(QWebElement* elem, QString name)
{
    qDebug() << "Artemis removed eventhandler for event: " << name << " tag name: "
             << elem->tagName() << " id: " << elem->attribute(QString("id")) << " title "
             << elem->attribute(QString("title")) << "class: " << elem->attribute("class") << endl;

    if (isNonInteractive(name)) {
        return;
    }

    mElementPointers.removeAt(mElementPointers.indexOf(QPair<QWebElement*, QString>(elem, name)));
    delete elem; //TODO look at these elements (QWebElements) and delete them when they are removed from the list
}

void ExecutionResultBuilder::slTimerAdded(int timerId, int timeout, bool singleShot)
{
    qDebug() << "Artemis::Timer " << timerId << " added";
    statistics()->accumulate("timers::registered", 1);
    mResult->mTimers.insert(timerId, QSharedPointer<Timer>(new Timer(timerId, timeout, singleShot)));
}

void ExecutionResultBuilder::slTimerRemoved(int timerId)
{
    qDebug() << "Artemis::Timer " << timerId << " removed";
    mResult->mTimers.remove(timerId);
}

void ExecutionResultBuilder::slStringEvaled(const QString exp)
{
    qDebug() << "WEBKIT: Evaled string: " << exp;
    mResult->mEvaledStrings << exp;
}

void ExecutionResultBuilder::slScriptCrashed(QString cause, intptr_t sourceID, int lineNumber)
{
    string lineNumberString = static_cast<ostringstream*>( &(ostringstream() << lineNumber) )->str();
    std::stringstream ss;
    ss << sourceID;
    qDebug() << "WEBKIT SCRIPT ERROR: " << cause << " line: " << lineNumber << " source: "
             << sourceID << endl;
}

void ExecutionResultBuilder::slAjaxCallbackHandlerAdded(int callbackId)
{
    qDebug() << "AJAX CALLBACK HANDLER ADDED" << endl;
    mResult->mAjaxCallbackHandlers.append(callbackId);
}

void ExecutionResultBuilder::slAjaxRequestInitiated(QUrl u, QString postData)
{
    QSharedPointer<AjaxRequest> req = QSharedPointer<AjaxRequest>(new AjaxRequest(u, postData));
    qDebug() << "Adding AJAX request: " << req;
    mResult->mAjaxRequest.insert(req);
}

void ExecutionResultBuilder::slJavascriptConstantStringEncountered(QString constant)
{
    statistics()->accumulate("WebKit::jsconstants", 1);
    mResult->mJavascriptConstantsObservedForLastEvent.insert(constant);
}

}
