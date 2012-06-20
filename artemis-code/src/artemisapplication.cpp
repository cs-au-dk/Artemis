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
#include <stdlib.h>

#include "artemisapplication.h"
#include "statistics/statsstorage.h"
#include "runtime/runtime.h"
#include "runtime/ajax/ajaxrequestlistener.h"
#include <runtime/browser/cookies/immutablecookiejar.h>

using namespace std;

namespace artemis {

    void printHeader();

    ArtemisApplication::ArtemisApplication(QObject *parent, QCoreApplication* qapp, ArtemisOptions* options) :
            QObject(parent)
    {
        this->artemis_options = options;
        this->app = qapp;

        srand(0); //Better way to get random numbers?

        AjaxRequestListener* ajaxRequestListner = new AjaxRequestListener(NULL);

        ImmutableCookieJar *immutable_cookie_jar = new ImmutableCookieJar(
        		artemis_options->get_preset_cookies(),
        		artemis_options->getURL()->host());
        ajaxRequestListner->setCookieJar(immutable_cookie_jar);

        WebKitExecutor* webkitExecutor = new WebKitExecutor(NULL,
        		artemis_options->get_preset_fields(),
        		artemis_options->get_listner(),
        		artemis_options->get_jquery_listener(),
        		ajaxRequestListner);

        generator = artemis_options->create_input_generator();
        mRuntime = new Runtime(this,
        		webkitExecutor,
        		generator,
        		artemis_options->prioritizer(),
        		artemis_options->termination(),
        		(MultiplexListener*)artemis_options->get_listner(),
        		artemis_options->dump_urls());

        QObject::connect(mRuntime, SIGNAL(sigTestingDone()),
                                 this, SLOT(sl_testingDone()));
    }

    void ArtemisApplication::run() {
        artemis::printHeader();

        artemis_options->print_presets();

        mRuntime->start(*artemis_options->getURL());
    }

    void ArtemisApplication::sl_testingDone() {

        app->exit(0);

    }
}
