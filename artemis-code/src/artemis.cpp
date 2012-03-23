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
#include <getopt.h>
#include <QCoreApplication>
#include <QDir>

#include "artemisoptions.h"
#include "inputgenerator/abstractinputgenerator.h"
#include "artemisapplication.h"
#include "exceptionhandlingqapp.h"

using namespace std;

namespace artemis {
void printHeader() {
    qDebug() << "Artemis - Automated tester for JavaScript";
    qDebug() << "Started: " << QDateTime::currentDateTime().toString();
    qDebug() << "Compilation date: " << EXE_BUILD_DATE;
    qDebug() << "-----\n" ;
}

ArtemisOptions* parseCmd(int argc, char *argv[]) {
    ArtemisOptions* res = new ArtemisOptions;
    int c;
    int index;
    while ((c = getopt (argc, argv, "rp:uf:t:c:i:a:")) != -1) {
        switch (c) {
        case 'f':
            res->parse_and_add_option_string(QString(optarg));
            break;
        case 'u':
            res->set_dump_urls(true);
            break;
        case 'p':
            {
                QDir ld = QDir(QString(optarg));
                res->dump_page_states(ld.absolutePath());
            }
            break;
        case 'r':
            res->set_recreate_page(true);
            break;
        case 't':
            res->set_proxy(QString(optarg));
            break;
        case 'c':
            res->set_preset_cookie(optarg);
            break;
        case 'i':
            printf("Encountered i!");
            res->set_number_of_iterations(QString(optarg));
            break;
        case 'a':
            // Support for http authentication
            // -a username:password
            res->set_authentication(QString(optarg));
            break;
        }
    }

    for (index = optind; index < argc; index++) {
        res->setURL(new QUrl(QString(argv[index])));
    }

    return res;
}

void artemisConsoleMessageHandler(QtMsgType type, const char *msg)
{
    switch (type) {
    case QtDebugMsg:
        fprintf(stdout, "%s\n", msg);
        break;
    case QtWarningMsg:
        fprintf(stdout, "Warning: %s\n", msg);
        break;
    case QtCriticalMsg:
        fprintf(stdout, "Critical: %s\n", msg);
        break;
    case QtFatalMsg:
        fprintf(stderr, "Fatal: %s\n", msg);
        abort();
    }
}
}

int main(int argc, char *argv[]) {
    qInstallMsgHandler(artemis::artemisConsoleMessageHandler);
    ExceptionHandlingQApp app(argc, argv);
    artemis::ArtemisOptions* cmdline_opts = artemis::parseCmd(argc, argv);
    if (cmdline_opts->getURL()->isEmpty()) {
        cerr << "ERROR: You must specify a URL" << endl;
        exit(1);
    }
    artemis::ArtemisApplication artemis_app(0,&app,cmdline_opts);
    artemis_app.run();

    return app.exec();
}
