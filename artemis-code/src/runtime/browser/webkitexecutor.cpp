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
#include <unistd.h>

#include <QtWebKit>
#include <QApplication>
#include <QStack>
#include <QDebug>
#include <qwebexecutionlistener.h>
#include <instrumentation/executionlistener.h>

#include "runtime/events/forms/formfield.h"
#include "runtime/events/domelementdescriptor.h"
#include "strategies/inputgenerator/targets/jquerylistener.h"
#include "runtime/input/baseinput.h"
#include "util/coverageutil.h"

#include "webkitexecutor.h"

using namespace std;

namespace artemis {

    WebKitExecutor::WebKitExecutor(QObject *parent,
    		QMap<QString,QString> presetFields,
            JQueryListener* jqueryListener,
            AjaxRequestListener* ajaxListener) :
            QObject(parent)
    {
    	current_result = NULL;

        mPresetFields = presetFields;
        mJquery = jqueryListener;

        ajax_listener = ajaxListener;
        ajax_listener->setParent(this);

        cov_list = new CoverageListener(this);

        webkit_listener = new QWebExecutionListener();
        webkit_listener->installWebKitExecutionListener(webkit_listener);

        // TODO cleanup in ajax stuff, we are handling ajax through AjaxRequestListener, the ajax_request signal and addAjaxCallHandler

        QObject::connect(webkit_listener, SIGNAL(script_crash(QString, intptr_t, int)),
                         this, SLOT(sl_script_crash(QString, intptr_t, int)));
        QObject::connect(webkit_listener, SIGNAL(ajax_request(QUrl, QString)),
                         this, SLOT(sl_ajax_request(QUrl, QString)));
        QObject::connect(webkit_listener, SIGNAL(loadedJavaScript(intptr_t, QString, QUrl, int)),
                         this, SLOT(sl_code_loaded(intptr_t, QString, QUrl, int)));
        
        QObject::connect(webkit_listener, SIGNAL(jqueryEventAdded(QString, QString, QString)),
                         mJquery, SLOT(sl_event_added(QString, QString, QString)));

        QObject::connect(webkit_listener, SIGNAL(loadedJavaScript(intptr_t, QString, QUrl, int)),
                         cov_list, SLOT(new_code(intptr_t, QString, QUrl, int)));
        QObject::connect(webkit_listener, SIGNAL(statementExecuted(intptr_t, std::string, int)),
                         cov_list, SLOT(statement_executed(intptr_t, std::string, int)));

        page = new ArtemisWebPage(this);
        page->setNetworkAccessManager(ajax_listener);

        QObject::connect(page, SIGNAL(loadFinished(bool)),
                         this, SLOT(slLoadFinished(bool)));

    }

    WebKitExecutor::~WebKitExecutor() {
        //delete current_conf;
        //delete current_result;
        delete page;
        delete cov_list;
    }

    void WebKitExecutor::executeSequence(QSharedPointer<ExecutableConfiguration*> conf) {
        qDebug() << "Artemis: Executing sequence" << endl;

        if (current_result != 0) {
            qDebug() << "Removing old result" << endl;

            current_result->disconnect();

            delete current_result;
        }

        current_result = new ExecutionResult(0);
        current_conf = conf;

        mJquery->reset();

        QObject::connect(webkit_listener, SIGNAL(addedEventListener(QWebElement*,QString)),
                            current_result, SLOT(newEventListener(QWebElement*,QString)));
        QObject::connect(webkit_listener, SIGNAL(removedEventListener(QWebElement*,QString)),
                            current_result, SLOT(removeEventListener(QWebElement*,QString)));

        QObject::connect(webkit_listener, SIGNAL(addedAjaxCallbackHandler(int)),
                            current_result, SLOT(addedAjaxCallbackHandler(int)));

        QObject::connect(webkit_listener, SIGNAL(addedTimer(int, int, bool)),
                            current_result, SLOT(sl_timer_added(int, int, bool)));
        QObject::connect(webkit_listener, SIGNAL(removedTimer(int)),
                            current_result, SLOT(sl_timer_removed(int)));

        QObject::connect(webkit_listener, SIGNAL(script_crash(QString,intptr_t,int)),
                            current_result, SLOT(sl_script_crash(QString,intptr_t,int)));
        QObject::connect(webkit_listener, SIGNAL(eval_call(QString)),
                            current_result, SLOT(sl_eval_string(QString)));

        //Load URL into WebKit
        qDebug() << "Trying to load: " << conf->getUrl().toString() << endl;
        page->mainFrame()->load(conf->getUrl());
    }

    void WebKitExecutor::slLoadFinished(bool ok) {

        if (!ok) {
            qDebug() << "WEBKIT: Website load failed!";

            current_result->make_load_failed();
            finishedExecutionSequence();

            exit(1);
            return;
        }

        qDebug() << "WEBKIT: Finished loading" << endl;

        //handle_ajax_callbacks();
        setup_initial();;
        do_exe();
        finishedExecutionSequence();
    }

    void WebKitExecutor::save_dom_state() {
        current_result->set_state_hash(qHash(page->mainFrame()->toHtml()));
        current_result->set_modfied_dom(page->mainFrame()->toHtml().localeAwareCompare(this->initial_page_state) != 0);
        current_result->setPageContents(page->mainFrame()->toHtml());
    }

    void WebKitExecutor::setup_initial() {
        //Save the page state
        this->initial_page_state = page->mainFrame()->toHtml();

        //Set preset formfields
        foreach (QString f , mPresetFields.keys()) {
            QWebElement elm = page->mainFrame()->findFirstElement(f);
            if (elm.isNull())
                continue;

            qDebug() << "Setting value " << mPresetFields[f] << "for element " << f << endl;
            elm.setAttribute("value", mPresetFields[f]);
        }

    }

    void WebKitExecutor::do_exe() {
        InputSequence* seq = current_conf->getInputSequence();
    
        foreach (BaseInput* input, seq->toList()) {
            qDebug() << "APPLY!" << endl;
            input->apply(this->page, this->webkit_listener);
            //Wait for any ajax stuff to finish
	    //            handle_ajax_callbacks();
        }
    }

    void WebKitExecutor::get_form_fields() {
        QSet<QWebFrame*> ff = all_frames();

        foreach(QWebFrame* f, ff) {
            QWebElementCollection inputs = f->findAllElements("input");
            foreach (QWebElement i, inputs) {
                FormFieldTypes f_type =  get_type_from_attr(i.attribute("type"));
                if (f_type == NO_INPUT)
                    continue;
                FormField* formf = new FormField(0, f_type, new DOMElementDescriptor(0, &i));
                current_result->add_form_field(formf);
                delete formf;
            }

            //Gather <textarea> elements
            QWebElementCollection textareas = f->findAllElements("textarea");
            foreach (QWebElement ta, textareas) {
                FormField* taf = new FormField(0, TEXT, new DOMElementDescriptor(0, &ta));
                current_result->add_form_field(taf);
                delete taf;
            }

            //Gather select tags
            QWebElementCollection selects = f->findAllElements("select");
            foreach (QWebElement ss, selects) {
                QSet<QString> options = get_select_options(ss);
                FormField* ssf = new FormField(0, FIXED_INPUT, new DOMElementDescriptor(0, &ss), options);
                current_result->add_form_field(ssf);
                delete ssf;
            }
        }
    }

    QSet<QString> WebKitExecutor::get_select_options(const QWebElement& e) {
        QSet<QString> res;
        QWebElementCollection options = e.findAll("option");
        foreach (QWebElement o, options) {
            QString value_attr = o.attribute("value");
            if (!value_attr.isEmpty())
                value_attr = o.toPlainText();
            if (value_attr.isEmpty()) {
                qWarning() << "WARN: Found empty option element in select, ignoring";
                continue;
            }
            res << value_attr;
        }
        return res;
    }

    QSet<QWebFrame*> WebKitExecutor::all_frames() {
        QSet<QWebFrame*> res;
        QWebFrame* main = page->mainFrame();
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

    void WebKitExecutor::finish_up() {
        if (current_result != 0) {
            qDebug() << "Removing old result" << endl;


            write_coverage_html(coverage());


            current_result->disconnect();

            delete current_result;
        }
    }

    void WebKitExecutor::finishedExecutionSequence() {
        get_form_fields();
        save_dom_state();

        current_result->finalize();

        emit sigExecutedSequence(current_conf, current_result);
    }

    CodeCoverage WebKitExecutor::coverage() {
        return cov_list->current_coverage();
    }

    void WebKitExecutor::sl_script_crash(QString ca, intptr_t id, int n) {
        qDebug() << "Script crashed";
    }

    void WebKitExecutor::sl_ajax_request(QUrl u, QString post_data) {
        AjaxRequest req = AjaxRequest(u,post_data);
        qDebug() << "Adding AJAX request: " << req;
        this->current_result->add_ajax_request(req);
    }

    void WebKitExecutor::sl_eval_called(QString eval_text) {
        qDebug() << "Dynamic code eval: " << eval_text;
    }

    void WebKitExecutor::sl_code_loaded(intptr_t _, QString src, QUrl url, int li) {
        qDebug() << "WebKitExecutor::sl_code_loaded" << endl;
    }
}
