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

ExecutionResultBuilder::ExecutionResultBuilder(ArtemisWebPagePtr page,
                                               ConcolicBenchmarkFeatures disabledFeatures,
                                               bool enableEventVisibilityFiltering)
    : QObject(NULL)
    , mPage(page)
    , mDisabledFeatures(disabledFeatures)
    , mEnableEventVisibilityFiltering(enableEventVisibilityFiltering)
{
    reset();
}

void ExecutionResultBuilder::reset()
{
    mResult = QSharedPointer<ExecutionResult>(new ExecutionResult());
    mElementPointers.clear();
    mTargetObjects.clear();
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

    if(mResult->mModifiedDom){
        emit sigDomModified(mPageStateAfterLoad, mResult->mPageContents);
    }

    return mResult;
}

void ExecutionResultBuilder::registerEventHandlersIntoResult()
{
    mResult->mEventHandlers = getCurrentEventHandlers();
}

QList<EventHandlerDescriptorConstPtr> ExecutionResultBuilder::getCurrentEventHandlers()
{
    QList<EventHandlerDescriptorConstPtr> handlerList;

    QList<QWebElement> userClickableElements;
    if (mEnableEventVisibilityFiltering) {
        userClickableElements = mPage->getAllUserClickableElementsAndAncestors();
    }

    QPair<QWebElement*, QString> p;
    foreach(p, mElementPointers) {
        if (getType(p.second) == UNKNOWN_EVENT) {
            qWarning() << "Ignoring unsupported event of type " << p.second << ", skipping";
            continue;
        }

        if (p.first->isNull()) {
            qWarning() << "Got event handler with NULL element." << mTargetObjects[p.first] << "is reciever.";
        }

        qDebug() << "Finalizing " << p.second << " xpath=" << p.first->xPath() << " _T: "
                 << p.first->attribute(QString("title"));
        EventHandlerDescriptorConstPtr handler = EventHandlerDescriptorConstPtr(new EventHandlerDescriptor(p.first, p.second, mTargetObjects[p.first]));

        if (handler->isInvalid()) {
            qWarning() << "element was invalid, skipping";
            continue;
        }

        // sometimes a handler is registered on a NULL element? and the descriptor infrastructure guesses a correct element to replace it
        // check if that guess is visible
        if (mEnableEventVisibilityFiltering) {
            QWebElement actualSource = handler->getDomElement()->getElement(mPage);

            // TODO: There are three visibility check methods available to use here.
            // !userClickableElements.contains(actualSource)    - Checks if the viewport includes a pixel of this element (slow and only works in the viewport).
            // !actualSource.isUserVisible()                    - Checks if the element has a bounding box.
            // !actualSource.isUserVisibleIncludingChildren()   - As above bu including children and text nodes.
            // The ideal solution would be some combination of these.

            if (!userClickableElements.contains(actualSource)) {
                Statistics::statistics()->accumulate("WebKit::events::skipped::visibility", 1);
                qDebug() << "Skipping EVENTHANDLER event (not user visible) =" << p.second
                         << "tag = " << actualSource.tagName()
                         << "id = " << actualSource.attribute(QString("id"))
                         << "title = " << actualSource.attribute(QString("title"))
                         << "class = " << actualSource.attribute("class")
                         << "visible = " << actualSource.isUserVisible()
                         << "xpath = " << actualSource.xPath();
                continue;
            }
        }

        Statistics::statistics()->accumulate("WebKit::events::added", 1);
        handlerList.append(handler);

    }

    return handlerList;
}

void ExecutionResultBuilder::registerFromFieldsIntoResult()
{
    mPage->updateFormIdentifiers(); // make sure that form identifiers (Artemis IDs) are set

    foreach(QWebFrame* frame, getAllFrames()) {
        // Gather all form field elements.
        // We select them all at once so we can maintain the DOM ordering of the form fields list.
        foreach(QWebElement field, frame->findAllElements("input, textarea, select")) {
            if(field.tagName().toLower() == "input") {
                FormFieldTypes type =  getTypeFromAttr(field.attribute("type"));

                if (type == NO_INPUT) {
                    if (mDisabledFeatures.testFlag(CONCRETE_VALUE_PROPERTY)) {
                        type = TEXT;
                    } else {
                        continue;
                    }
                }

                DOMElementDescriptorConstPtr elementDescriptor = DOMElementDescriptorConstPtr(new DOMElementDescriptor(&field));
                FormFieldDescriptorPtr fieldDescriptor = FormFieldDescriptorPtr(new FormFieldDescriptor(type, elementDescriptor));

                mResult->mFormFields.append(fieldDescriptor);

            } else if(field.tagName().toLower() == "textarea") {
                FormFieldDescriptorPtr taf = FormFieldDescriptorPtr(new FormFieldDescriptor(TEXT, DOMElementDescriptorConstPtr(new DOMElementDescriptor(&field))));
                mResult->mFormFields.append(taf);

            } else if(field.tagName().toLower() == "select") {
                QSet<QString> options = getSelectOptions(field);
                FormFieldDescriptorPtr ssf = FormFieldDescriptorPtr(new FormFieldDescriptor(FIXED_INPUT, DOMElementDescriptorConstPtr(new DOMElementDescriptor(&field)), options));
                mResult->mFormFields.append(ssf);

            }
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

void ExecutionResultBuilder::slEventListenerAdded(QWebElement* elem, QString eventName, QString targetObject)
{
    Q_CHECK_PTR(elem);

    qDebug() << "Detected EVENTHANDLER event =" << eventName
             << "tag = " << elem->tagName()
             << "id = " << elem->attribute(QString("id"))
             << "title = " << elem->attribute(QString("title"))
             << "class = " << elem->attribute("class")
             << "visible = " << elem->isUserVisible()
             << "xpath = " << elem->xPath()
             << "isNull = " << elem->isNull();

    if (isNonInteractive(eventName)) {
        return;
    }

    mElementPointers.append(QPair<QWebElement*, QString>(elem, eventName));
    mTargetObjects.insert(elem, targetObject);
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
    mTargetObjects.remove(elem);
    delete elem; //TODO look at these elements (QWebElements) and delete them when they are removed from the list
}

void ExecutionResultBuilder::slTimerAdded(int timerId, int timeout, bool singleShot)
{
    qDebug() << "Artemis::Timer " << timerId << " added";
    Statistics::statistics()->accumulate("timers::registered", 1);
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
    Statistics::statistics()->accumulate("ajax::XMLHttpRequest::sent", 1);
    mResult->mAjaxRequest.insert(req);
}

void ExecutionResultBuilder::slJavascriptConstantStringEncountered(QString constant)
{
    Statistics::statistics()->accumulate("WebKit::jsconstants", 1);
    mResult->mJavascriptConstantsObservedForLastEvent.insert(constant);
}

}
