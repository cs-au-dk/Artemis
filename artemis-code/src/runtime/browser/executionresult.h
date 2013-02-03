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
#ifndef EXECUTIONRESULT_H
#define EXECUTIONRESULT_H

#include <QObject>
#include <QtWebKit>
#include <QSet>
#include <QPair>
#include <QList>

#include "runtime/events/eventhandlerdescriptor.h"
#include "runtime/events/forms/formfield.h"
#include "runtime/browser/timer.h"
#include "artemisglobals.h"
#include "runtime/ajax/ajaxrequest.h"
#include "artemiswebpage.h"

namespace artemis
{

class ExecutionResult : public QObject
{
    Q_OBJECT

public:
    ExecutionResult(QObject* parent);
    ExecutionResult(QObject* parent, const ExecutionResult* other);

    QSet<EventHandlerDescriptor*> eventHandlers() const;

    QSet<QSharedPointer<const FormField> > formFields() const;
    void addFormFields(QSet<QSharedPointer<const FormField> > f);
    void addFormField(QSharedPointer<const FormField> f);

    void addAjaxRequest(AjaxRequest req);
    QSet<AjaxRequest> ajaxRequest() const;
    void makeLoadFailed();
    bool modifedDom() const;
    void setModfiedDom(bool b) ;
    void setStateHash(long hash);
    long pageStateHash() const;
    QSet<QString> evalStrings();
    QList<int> ajaxCallbackHandlers() const;
    QList<QSharedPointer<Timer> > getTimers() const;
    QString getPageContents() const;
    void setPageContents(QString content);

    /**
      Invoke this method when the page containing the elements is done loading.
      */
    void finalize();

    QDebug friend operator<<(QDebug dbg, const ExecutionResult& e);

private:
    QSet<EventHandlerDescriptor*> mEventHandlers;
    QSet<QPair<QWebElement*, QString> > elementPointers;
    QSet<QSharedPointer<const FormField> > mFormFields;
    bool final;
    bool isCrashState;
    QString crashCause;
    intptr_t crashSourceID;
    int crashLineNumber;
    bool mModfiedDom;
    long stateHash;
    QSet<AjaxRequest> mAjaxRequest;
    QSet<QString> evaledStrings;
    QList<int> mAjaxCallbackHandlers;
    QMap<int, QSharedPointer<Timer> > mTimers; // <timerId, Timer>
    QString mPageContents;

public slots:
    void newEventListener(QWebElement* elem, QString name);
    void removeEventListener(QWebElement* elem, QString name);
    void slScriptCrash(QString cause, intptr_t sourceID, int lineNumber);
    void slEvalString(const QString);
    void addedAjaxCallbackHandler(int callbackId);

    void slTimerAdded(int timerId, int timeout, bool singleShot);
    void slTimerRemoved(int timerId);
};
}

#endif // EXECUTIONRESULT_H
