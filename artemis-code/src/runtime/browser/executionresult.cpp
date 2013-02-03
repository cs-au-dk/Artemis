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
#include <iostream>

#include "runtime/events/eventypes.h"
#include "statistics/statsstorage.h"

#include "executionresult.h"

using namespace std;

namespace artemis
{

ExecutionResult::ExecutionResult(QObject* parent) : QObject(parent)
{
    final = false;
    isCrashState = false;
    crashCause = "";
    crashLineNumber = 0;
    crashSourceID = 0;
    mModfiedDom = false;
    stateHash = 0;
}

ExecutionResult::ExecutionResult(QObject* parent, const ExecutionResult* other) : QObject(parent)
{
    this->final = other->final;
    this->mEventHandlers = other->mEventHandlers;
    this->elementPointers = other->elementPointers;
    this->isCrashState = other->isCrashState;
    this->mModfiedDom = other->mModfiedDom;
    this->stateHash = other->stateHash;
    this->mAjaxRequest = other->mAjaxRequest;
    this->evaledStrings = other->evaledStrings;

    if (other->isCrashState) {
        this->isCrashState = other->isCrashState;
        this->crashCause = other->crashCause;
        this->crashLineNumber = other->crashLineNumber;
        this->crashSourceID = other->crashSourceID;
    }

    this->mTimers = QMap<int, QSharedPointer<Timer> >(other->mTimers);
    this->mAjaxCallbackHandlers = QList<int>(other->mAjaxCallbackHandlers);
}

void ExecutionResult::newEventListener(QWebElement* elem, QString name)
{
    Q_CHECK_PTR(elem);
    Q_ASSERT(!final);

    qDebug() << "Artemis detected new eventhandler for event: " << name << " tag name: "
             << elem->tagName() << " id: " << elem->attribute(QString("id")) << " title "
             << elem->attribute(QString("title")) << "class: " << elem->attribute("class") << endl;

    if (isNonInteractive(name))
        { return; }

    elementPointers.insert(QPair<QWebElement*, QString>(elem, name));
}

void ExecutionResult::setPageContents(QString content)
{
    mPageContents = content;
}

QString ExecutionResult::getPageContents() const
{
    return mPageContents;
}

void ExecutionResult::removeEventListener(QWebElement* elem, QString name)
{
    qDebug() << "Artemis removed eventhandler for event: " << name << " tag name: "
             << elem->tagName() << " id: " << elem->attribute(QString("id")) << " title "
             << elem->attribute(QString("title")) << "class: " << elem->attribute("class") << endl;

    if (isNonInteractive(name))
        { return; }

    bool removed = elementPointers.remove(QPair<QWebElement*, QString>(elem, name));

    Q_ASSERT(removed);
}

void ExecutionResult::addedAjaxCallbackHandler(int callbackId)
{
    qDebug() << "AJAX CALLBACK HANDLER ADDED" << endl;
    mAjaxCallbackHandlers.append(callbackId);
}

QList<int> ExecutionResult::ajaxCallbackHandlers() const
{
    return mAjaxCallbackHandlers;
}

void ExecutionResult::finalize()
{
    Q_ASSERT(mEventHandlers.isEmpty());
    Q_ASSERT(!final);

    if (isCrashState) {
        final = true;
        return;
    }

    QPair<QWebElement*, QString> p;
    foreach(p, elementPointers) {
        if (getType(p.second) == UNKNOWN_EVENT) {
            continue; //qWarning() << ""
            //TODO: Save strange events somewhere.
        }

        qDebug() << "Finalizing " << p.second << "  " << p.first->tagName() << " _T: "
                 << p.first->attribute(QString("title"));

        if (/*p.first->tagName().isEmpty()*/p.first->isNull()) {
            qWarning()
                    << "WEBKIT WARN: Got event handler with NULL element. Assuming document is reciever";
            //continue;
        }

        EventHandlerDescriptor* handler = new EventHandlerDescriptor(this, p.first, p.second);

        if (handler->isInvalid())
            { qDebug() << "WARN: element was invalid, ignoring"; }
        else
            { mEventHandlers.insert(handler); }
    }
    final = true;
    elementPointers.clear();
}

QSet<const FormField*> ExecutionResult::formFields() const
{
    Q_ASSERT(final);
    return mFormFields;
}

void ExecutionResult::addAjaxRequest(AjaxRequest req)
{
    Q_ASSERT(!final);
    //this->mAjaxRequest << req;
}

QSet<AjaxRequest> ExecutionResult::ajaxRequest() const
{
    return this->mAjaxRequest;
}

void ExecutionResult::addFormField(const FormField* f)
{
    Q_ASSERT(!final);

    FormField* formField = new FormField(this, f);
    mFormFields.insert(formField);
}

void ExecutionResult::addFormFields(const QSet<FormField*>& fields)
{
    Q_ASSERT(!final);

    foreach(FormField * field, fields) {
        this->addFormField(field);
    }
}

QSet<EventHandlerDescriptor*> ExecutionResult::eventHandlers() const
{
    Q_ASSERT(final);
    return mEventHandlers;
}

void ExecutionResult::makeLoadFailed()
{
    isCrashState = true;
    crashCause = "Webkit failed to load the page";
    crashSourceID = 0;
    crashLineNumber = 0;
}

void ExecutionResult::slScriptCrash(QString cause, intptr_t sourceID, int lineNumber)
{
    qDebug() << "WEBKIT SCRIPT ERROR: " << cause << " line: " << lineNumber << " source: "
             << sourceID << endl;

    this->crashCause = cause;
    this->crashSourceID = sourceID;
    this->crashLineNumber = lineNumber;
    isCrashState = true;
}

void ExecutionResult::slEvalString(const QString exp)
{
    Q_ASSERT(!final);
    qDebug() << "WEBKIT: Evaled string: " << exp;
    this->evaledStrings << exp;
}

QSet<QString> ExecutionResult::evalStrings()
{
    return this->evaledStrings;
}

void ExecutionResult::setModfiedDom(bool b)
{
    Q_ASSERT(!final);
    this->mModfiedDom = b;
}

QDebug operator<<(QDebug dbg, const ExecutionResult& e)
{
    if (e.final) {
        if (e.isCrashState) {
            dbg.nospace() << "CRASH STATE: " << e.crashCause;
        }
        else {
            dbg.nospace() << "Event handlers: " << e.mEventHandlers << "\n";
            dbg.nospace() << "Form fields   : " << e.mFormFields << "\n";
            dbg.nospace() << "Modfied dom   : " << e.mModfiedDom << "\n";
            dbg.nospace() << "Ajax requests : " << e.mAjaxRequest << "\n";
            dbg.nospace() << "Evaled strings: " << e.evaledStrings;
        }
    }
    else
        dbg.nospace() << "Unfinalized ExecutionResult with " << e.elementPointers.size()
                      << " events so far";

    return dbg.space();
}

void ExecutionResult::setStateHash(long hash)
{
    Q_ASSERT(!final);
    this->stateHash = hash;
}

long ExecutionResult::pageStateHash() const
{
    Q_ASSERT(final);
    return this->stateHash;

}

bool ExecutionResult::modifedDom() const
{
    Q_ASSERT(final);
    return this->mModfiedDom;
}

void ExecutionResult::slTimerAdded(int timerId, int timeout, bool singleShot)
{
    qDebug() << "Artemis::Timer " << timerId << " added";
    statistics()->accumulate("timers::registered", 1);
    this->mTimers.insert(timerId, QSharedPointer<Timer>(new Timer(timerId, timeout, singleShot)));
}

void ExecutionResult::slTimerRemoved(int timerId)
{
    qDebug() << "Artemis::Timer " << timerId << " removed";
    this->mTimers.remove(timerId);
}

QList<QSharedPointer<Timer> > ExecutionResult::getTimers() const
{
    return this->mTimers.values();
}

}
