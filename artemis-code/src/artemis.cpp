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
#include <QApplication>
#include <QDir>
#include <QUrl>

#include "builder/options.h"
#include "artemisapplication.h"

using namespace std;

void printHeader() {
    qDebug() << "Artemis - Automated tester for JavaScript";
    qDebug() << "Started: " << QDateTime::currentDateTime().toString();
    qDebug() << "Compilation date: " << EXE_BUILD_DATE;
    qDebug() << "-----\n" ;
}

QUrl parseCmd(int argc, char *argv[], artemis::Options& options) {

    char c;
    while ((c = getopt(argc, argv, "rp:f:t:c:i:")) != -1) {

    	switch (c) {

        case 'f':
        {
        	QStringList rawformfield = QString(optarg).split("=");
        	Q_ASSERT(rawformfield.size() == 2);
        	options.presetFormfields.insert(rawformfield.at(0), rawformfield.at(1));
            break;
        }

        case 'p':
        {
            QDir ld = QDir(QString(optarg));
            options.dumpPageStates = "k";
            break;
        }

        case 'r':
        {
        	options.recreatePage = true;
            break;
        }

        case 't':
        {
        	options.useProxy = QString(optarg);
            break;
        }

        case 'c':
        {
        	QStringList parts = QString(optarg).split("=");
        	options.presetCookies.insert(parts.at(0), parts.at(1));
            break;
        }

        case 'i':
        {
        	options.iterationLimit = QString(optarg).toInt();
            break;
        }

        }
    }

    if (optind > argc) {
    	cerr << "ERROR: You must specify a URL" << endl;
    	exit(1);
    }

    QStringList rawurl = QString(argv[optind]).split("@");
    QUrl url = rawurl.last();

    if (rawurl.size() > 1) {
    	QStringList rawauth = rawurl.first().split(":");
    	url.setUserName(rawauth.first());
    	url.setPassword(rawauth.last());
    }

    return url;
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

int main(int argc, char *argv[]) {
	printHeader();

	qInstallMsgHandler(artemisConsoleMessageHandler);

    QApplication app(argc, argv);

    artemis::Options options;
    QUrl url = parseCmd(argc, argv, options);

    artemis::ArtemisApplication artemis_app(0, &app, options, url);
    artemis_app.run(url);

    return app.exec();
}
