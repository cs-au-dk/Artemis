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

ExecutionResult::ExecutionResult(QObject *parent) :
    QObject(parent)
{
    final = false;
    is_crash_state = false;
    crash_cause = "";
    crash_lineNumber = 0;
    crash_sourceID = 0;
}

ExecutionResult::ExecutionResult(const ExecutionResult& other) :
    QObject(0)
{
    this->final = other.final;
    this->m_event_handlers = other.m_event_handlers;
    this->element_pointers = other.element_pointers;
    this->is_crash_state = other.is_crash_state;
    this->m_urls = other.m_urls;
    this->m_modfied_dom = other.m_modfied_dom;
    this->state_hash = other.state_hash;
    this->m_ajax_request = other.m_ajax_request;
    this->evaled_strings = other.evaled_strings;
    if (other.is_crash_state) {
        this->is_crash_state = other.is_crash_state;
        this->crash_cause = other.crash_cause;
        this->crash_lineNumber = other.crash_lineNumber;
        this->crash_sourceID = other.crash_sourceID;
    }
    this->m_timers = QMap<int, Timer>(other.m_timers);
    this->m_ajax_callback_handlers = QList<int>(other.m_ajax_callback_handlers);
}

void ExecutionResult::newEventListener(QWebElement *elem, QString name)
{
    Q_CHECK_PTR(elem);
    Q_ASSERT(!final);

    qDebug() << "Artemis detected new eventhandler for event: " << name << " tag name: "
        << elem->tagName() << " id: " << elem->attribute(QString("id")) << " title "
        << elem->attribute(QString("title")) << "class: " << elem->attribute("class") << endl;
    if (is_non_interactive(name))
        return;

    element_pointers.insert(QPair<QWebElement*, QString>(elem, name));
}

void ExecutionResult::setPageContents(QString content)
{
    mPageContents = content;
}

QString ExecutionResult::getPageContents() const
{
    return mPageContents;
}

void ExecutionResult::removeEventListener(QWebElement *elem, QString name)
{
    qDebug() << "Artemis removed eventhandler for event: " << name << " tag name: "
        << elem->tagName() << " id: " << elem->attribute(QString("id")) << " title "
        << elem->attribute(QString("title")) << "class: " << elem->attribute("class") << endl;

    if (is_non_interactive(name))
        return;

    bool removed = element_pointers.remove(QPair<QWebElement*, QString>(elem, name));

    Q_ASSERT(removed);
}

void ExecutionResult::addedAjaxCallbackHandler(int callbackId)
{
    qDebug() << "AJAX CALLBACK HANDLER ADDED" << endl;
    m_ajax_callback_handlers.append(callbackId);
}

QList<int> ExecutionResult::ajaxCallbackHandlers() const
{
    return m_ajax_callback_handlers;
}

void ExecutionResult::finalize()
{
    Q_ASSERT(m_event_handlers.isEmpty());
    Q_ASSERT(!final);
    if (is_crash_state) {
        final = true;
        return;
    }
    QPair<QWebElement*, QString> p;
    foreach (p, element_pointers) {
        if (get_type(p.second) == UNKNOWN_EVENT) {
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

        EventHandlerDescriptor handler(p.first, p.second);

        if (handler.is_invalid())
            qDebug() << "WARN: element was invalid, ignoring";
        else
            m_event_handlers.insert(handler);
    }
    final = true;
    element_pointers.clear();
}

QSet<FormField> ExecutionResult::form_fields() const
{
    Q_ASSERT(final);
    return m_form_fields;
}

void ExecutionResult::add_ajax_request(AjaxRequest req)
{
    Q_ASSERT(!final);
    //this->m_ajax_request << req;
}

QSet<AjaxRequest> ExecutionResult::ajax_request() const
{
    return this->m_ajax_request;
}

void ExecutionResult::add_form_field(FormField f)
{
    Q_ASSERT(!final);
    m_form_fields << f;
}

void ExecutionResult::add_form_fields(const QSet<FormField>& f)
{
    Q_ASSERT(!final);
    m_form_fields += f;
}

void ExecutionResult::add_urls(const QSet<QUrl>& u)
{
    Q_ASSERT(!final);
    m_urls += u;
}

QSet<EventHandlerDescriptor> ExecutionResult::event_handlers() const
{
    Q_ASSERT(final);
    return m_event_handlers;
}

QSet<QUrl> ExecutionResult::urls() const
{
    return this->m_urls;
}

void ExecutionResult::add_url(const QUrl url)
{
    Q_ASSERT(!final);
    m_urls << url;
}

void ExecutionResult::make_load_failed()
{
    is_crash_state = true;
    crash_cause = "Webkit failed to load the page";
    crash_sourceID = 0;
    crash_lineNumber = 0;
}

uint ExecutionResult::hashcode() const
{
    Q_ASSERT(final);
    if (is_crash_state) {
        return 17 * qHash(this->crash_cause) + 23 * crash_lineNumber;
    }
    return 17 * qHash(m_event_handlers) + 23 * qHash(m_form_fields) + 27 * qHash(m_urls)
        + 9 * state_hash + 13 * qHash(m_ajax_request) + 5 * qHash(evaled_strings);
}

bool ExecutionResult::operator==(ExecutionResult& other)
{
    Q_ASSERT(final);
    return m_event_handlers == other.m_event_handlers && m_form_fields == other.m_form_fields
        && is_crash_state == other.is_crash_state && crash_cause == other.crash_cause
        && crash_lineNumber == other.crash_lineNumber && crash_sourceID == other.crash_sourceID
        && m_urls == other.m_urls && m_modfied_dom == other.m_modfied_dom
        && state_hash == other.state_hash && m_ajax_request == other.m_ajax_request
        && evaled_strings == other.evaled_strings;
}

ExecutionResult &ExecutionResult::operator=(const ExecutionResult &other)
{
    Q_ASSERT(final);
    this->m_event_handlers = other.m_event_handlers;
    this->m_form_fields = other.m_form_fields;
    this->is_crash_state = other.is_crash_state;
    this->crash_cause = other.crash_cause;
    this->crash_lineNumber = other.crash_lineNumber;
    this->crash_sourceID = other.crash_sourceID;
    this->m_urls = other.m_urls;
    this->m_modfied_dom = other.m_modfied_dom;
    this->state_hash = other.state_hash;
    this->m_ajax_request = other.m_ajax_request;
    this->evaled_strings = other.evaled_strings;
    this->m_timers = other.m_timers;
    this->m_ajax_callback_handlers = other.m_ajax_callback_handlers;
    return *this;
}

void ExecutionResult::sl_script_crash(QString cause, intptr_t sourceID, int lineNumber)
{
    qDebug() << "WEBKIT SCRIPT ERROR: " << cause << " line: " << lineNumber << " source: "
        << sourceID << endl;

    this->crash_cause = cause;
    this->crash_sourceID = sourceID;
    this->crash_lineNumber = lineNumber;
    is_crash_state = true;
}

void ExecutionResult::sl_eval_string(const QString exp)
{
    Q_ASSERT(!final);
    qDebug() << "WEBKIT: Evaled string: " << exp;
    this->evaled_strings << exp;
}

QSet<QString> ExecutionResult::eval_strings()
{
    return this->evaled_strings;
}

void ExecutionResult::set_modfied_dom(bool b)
{
    Q_ASSERT(!final);
    this->m_modfied_dom = b;
}

QDebug operator<<(QDebug dbg, const ExecutionResult &e)
{
    if (e.final) {
        if (e.is_crash_state) {
            dbg.nospace() << "CRASH STATE: " << e.crash_cause;
        }
        else {
            dbg.nospace() << "Event handlers: " << e.m_event_handlers << "\n";
            dbg.nospace() << "Form fields   : " << e.m_form_fields << "\n";
            dbg.nospace() << "Urls          : " << e.m_urls << "\n";
            dbg.nospace() << "Modfied dom   : " << e.m_modfied_dom << "\n";
            dbg.nospace() << "Ajax requests : " << e.m_ajax_request << "\n";
            dbg.nospace() << "Evaled strings: " << e.evaled_strings;
        }
    }
    else
        dbg.nospace() << "Unfinalized ExecutionResult with " << e.element_pointers.size()
            << " events so far";
    return dbg.space();
}

void ExecutionResult::set_state_hash(long hash)
{
    Q_ASSERT(!final);
    this->state_hash = hash;
}

long ExecutionResult::page_state_hash() const
{
    Q_ASSERT(final);
    return this->state_hash;

}

bool ExecutionResult::modifed_dom() const
{
    Q_ASSERT(final);
    return this->m_modfied_dom;
}

void ExecutionResult::sl_timer_added(int timer_id, int timeout, bool single_shot)
{
    qDebug() << "Artemis::Timer " << timer_id << " added";
    statistics()->accumulate("timers::registered", 1);
    this->m_timers.insert(timer_id, Timer(timer_id, timeout, single_shot));
}

void ExecutionResult::sl_timer_removed(int timer_id)
{
    qDebug() << "Artemis::Timer " << timer_id << " removed";
    this->m_timers.remove(timer_id);
}

QList<Timer> ExecutionResult::get_timers() const
{
    return this->m_timers.values();
}
}
