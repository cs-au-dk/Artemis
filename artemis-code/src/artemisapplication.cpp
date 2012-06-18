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
#include "coverage/coveragetooutputstream.h"
#include "statistics/statsstorage.h"
#include "statistics/writers/pretty.h"
#include "runtime/runtime.h"

using namespace std;

namespace artemis {

    void printHeader();

    ArtemisApplication::ArtemisApplication(QObject *parent, QCoreApplication* qapp, ArtemisOptions* options) :
            QObject(parent)
    {
        this->artemis_options = options;
        this->app = qapp;
        s_list = new SourceLoadingListener();

        srand(0); //Better way to get random numbers?

        generator = artemis_options->create_input_generator();
        mRuntime = new Runtime(this, artemis_options, generator);

        QObject::connect(mRuntime, SIGNAL(sigTestingDone()),
                                 this, SLOT(sl_testingDone()));
    }

    void ArtemisApplication::run() {
        artemis::printHeader();

        artemis_options->add_artemis_execution_listner(s_list);
        artemis_options->print_presets();

        mRuntime->start();
    }

    void ArtemisApplication::sl_testingDone() {
        cout << "Artemis: Testing done..." << endl;

        if (this->artemis_options->dump_urls()) {
            cout << "The following URLs were encountered:\n";
            mRuntime->urlsCollected().print_urls();
        }

        cout << "\n\n === Coverage information for execution === \n";
        write_coverage_report(cout, mRuntime->coverage());
        
        cout << "\n==== Source code loaded ====\n";
        s_list->print_results();
        cout << "\n\n";

        cout << "\n=== Statistics ===\n";
        StatsPrettyWriter::write(cout, statistics());
        cout << "\n=== Statistics END ===\n";
        cout << endl;
        
        qDebug() << "Artemis terminated on: " << QDateTime::currentDateTime().toString() << endl;
        qDebug() << "Build timestamp: " << EXE_BUILD_DATE << endl;

        app->exit(0);

    }
}
