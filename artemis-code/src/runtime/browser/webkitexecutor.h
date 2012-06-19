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

#ifndef WEBKITEXECUTOR_H
#define WEBKITEXECUTOR_H

#include <QObject>
#include <QSemaphore>
#include <QtWebKit>
#include <QtWebKit/qwebexecutionlistener.h>

#include "artemisoptions.h"
#include "artemisglobals.h"
#include "executionresult.h"
#include "artemiswebpage.h"
#include "runtime/executableconfiguration.h"
#include "coverage/coveragelistener.h"
#include "listeners/artemistopexecutionlistener.h"
#include "runtime/ajax/ajaxrequestlistener.h"

#include "runtime/browser/webkitwrapper.h"

namespace artemis {

    class WebKitExecutor : public QObject
    {
        Q_OBJECT
    public:
        explicit WebKitExecutor(QObject *parent = 0, ArtemisOptions* options = 0, ArtemisTopExecutionListener* listener = 0);
        ~WebKitExecutor();
        void executeSequence(ExecutableConfiguration* conf);
        QWebExecutionListener* webkit_listener;
        CodeCoverage coverage();
        void finish_up();

    private:
        void setup();
        void finished_sequence();
        void get_form_fields();
        void get_links();
        QSet<QWebFrame*> all_frames();
        QSet<QString> get_select_options(const QWebElement&);
        void do_exe();
        void handle_ajax_callbacks();
        void setup_initial();
        void save_dom_state();

        ArtemisOptions* artemis_options;
        ArtemisWebPage* page;
        ExecutionResult* current_result;
        ExecutableConfiguration* current_conf;
        CoverageListener* cov_list;
        QString initial_page_state;
        ArtemisTopExecutionListener* execution_listener;
        AjaxRequestListener ajax_listener;
        JQueryListener* jquery;

        WebKitWrapper* mWebkitWrapper;

    signals:
        void sigExecutedSequence(ExecutableConfiguration* conf, ExecutionResult res);

    public slots:
        void sl_loadFinished(bool ok);
        void sl_script_crash(QString, intptr_t, int);
        void sl_ajax_request(QUrl, QString post_data);
        void sl_eval_called(QString eval_text);
        void sl_code_loaded(intptr_t, QString, QUrl, int);
    };

}
#endif // WEBKITEXECUTOR_H
