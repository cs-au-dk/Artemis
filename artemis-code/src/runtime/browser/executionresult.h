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

namespace artemis {

class ExecutionResult : public QObject
{
    Q_OBJECT

    public:
        ExecutionResult(QObject *parent);
        ExecutionResult(QObject *parent, const ExecutionResult* other);

        QSet<EventHandlerDescriptor*> event_handlers() const;

        QSet<FormField*> form_fields() const;
        void add_form_fields(const QSet<FormField*>& f);
        void add_form_field(const FormField* f);

        void add_urls(const QSet<QUrl>& u);
        void add_ajax_request(AjaxRequest req);
        QSet<AjaxRequest> ajax_request() const;
        QSet<QUrl> urls() const;
        void make_load_failed();
        bool modifed_dom() const;
        void set_modfied_dom(bool b) ;
        void set_state_hash(long hash);
        long page_state_hash() const;
        QSet<QString> eval_strings();
        QList<int> ajaxCallbackHandlers() const;
        QList<Timer> get_timers() const;
        QString getPageContents() const;
        void setPageContents(QString content);

        /**
          Invoke this method when the page containing the elements is done loading.
          */
        void finalize();

        QDebug friend operator<<(QDebug dbg, const ExecutionResult &e);

    private:
        QSet<EventHandlerDescriptor*> m_event_handlers;
        QSet<QPair<QWebElement*,QString> > element_pointers;
        QSet<FormField*> m_form_fields;
        QSet<QUrl> m_urls;
        bool final;
        bool is_crash_state;
        QString crash_cause;
        intptr_t crash_sourceID;
        int crash_lineNumber;
        bool m_modfied_dom;
        long state_hash;
        QSet<AjaxRequest> m_ajax_request;
        QSet<QString> evaled_strings;
        QList<int> m_ajax_callback_handlers;
        QMap<int, Timer> m_timers; // <timer_id, Timer>
        QString mPageContents;

    public slots:
        void newEventListener(QWebElement* elem, QString name);
        void removeEventListener(QWebElement* elem, QString name);
        void sl_script_crash(QString cause, intptr_t sourceID, int lineNumber);
        void add_url(const QUrl url);
        void sl_eval_string(const QString);
        void addedAjaxCallbackHandler(int callbackId);

        void sl_timer_added(int timer_id, int timeout, bool single_shot);
        void sl_timer_removed(int timer_id);
};
}

#endif // EXECUTIONRESULT_H
