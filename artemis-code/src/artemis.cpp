/*
 * Copyright 2012 Aarhus University
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
#include <iostream>
#include <stdlib.h>
#include <getopt.h>
#include <string>
#include <QDir>
#include <QUrl>
#include <QApplication>

#include "exceptionhandlingqapp.h"
#include "runtime/options.h"
#include "artemisapplication.h"
#include "util/loggingutil.h"

using namespace std;

QUrl parseCmd(int argc, char* argv[], artemis::Options& options)
{

    std::string usage = "\n"
           "artemis [-i <n>][-c <URL>][-t <URL>][-r][-u][-p <path>] <url>\n"
           "\n"
           "Test the JavaScript application found at <url>.\n"
           "\n"
           "-i <n>   : Iterations - Artemis will generate and execute <n>\n"
           "           sequences of events. Default is 4.\n"
           "\n"
           "-c <URl> : Cookies - // TODO\n"
           "\n"
           "-t <URL> : Proxy - // TODO\n"
           "\n"
           "-r       : set_recreate_page(true) // TODO\n"
           "\n"
           "-p       : dump_page_states(<path>) // TODO\n"
           "\n"
           "-s       : Enable DOM state checking\n"
           "\n"
           "--strategy-form-input-generation <strategy>:\n"
           "           Select form input generation strategy.\n"
           "\n"
           "           javascript-constants - select form inputs based in observed JavaScript constants\n"
           "           random - (default) random inputs\n"
           "\n"
           "--coverage-report <report-type>:\n"
           "           Select code coverage report formatting.\n"
           "\n"
           "           html - HTML report dumped in the folder you run Artemis from\n"
           "           stdout - text report is printed to std out\n"
           "           none - (default) code coverage report is omitted\n"
           "\n"
           "--strategy-priority <strategy>:\n"
           "           Select priority strategy.\n"
           "\n"
           "           constant - (default) assign the same priority to new configurations\n"
           "           random - assign a random priority to new configurations\n"
           "           coverage - assign higher priority to configurations with low coverage\n"
           "           readwrite - use read/write-sets for JavaScript properties to assign priorities\n\n";

    struct option long_options[] = {
        {"strategy-form-input-generation", required_argument, NULL, 'x'},
        {"coverage-report", required_argument, NULL, 'y'},
        {"strategy-priority", required_argument, NULL, 'z'},
        {"help", no_argument, NULL, 'h'},
        {0, 0, 0, 0}
    };

    int option_index = 0;
    char c;
    artemis::Log::addLogLevel(artemis::INFO);
    artemis::Log::addLogLevel(artemis::FATAL);

    while ((c = getopt_long(argc, argv, "hsrp:f:t:c:i:v:", long_options, &option_index)) != -1) {

        switch (c) {

        case 'h': {
            std::cout << usage;
            exit(0);
        }

        case 'f': {
            QStringList rawformfield = QString(optarg).split("=");
            Q_ASSERT(rawformfield.size() == 2);
            options.presetFormfields.insert(rawformfield.at(0), rawformfield.at(1));
            break;
        }

        case 'p': {
            QDir ld = QDir(QString(optarg));
            options.dumpPageStates = "k";
            break;
        }

        case 'r': {
            options.recreatePage = true;
            break;
        }

        case 't': {
            options.useProxy = QString(optarg);
            break;
        }

        case 'c': {
            QStringList parts = QString(optarg).split("=");
            options.presetCookies.insert(parts.at(0), parts.at(1));
            break;
        }

        case 'i': {
            options.iterationLimit = QString(optarg).toInt();
            break;
        }

        case 's': {
            options.disableStateCheck = false;
            break;
        }

        case 'x': {

            if (string(optarg).compare("javascript-constants") == 0) {
                options.formInputGenerationStrategy = artemis::ConstantString;
            } else if (string(optarg).compare("random") == 0) {
                options.formInputGenerationStrategy = artemis::Random;
            } else {
                cerr << "ERROR: Invalid strategy " << optarg << endl;
                exit(1);
            }

            break;

        }

        case 'y': {
            if (string(optarg).compare("html") == 0) {
                options.outputCoverage = artemis::HTML;
            } else if (string(optarg).compare("stdout") == 0) {
                options.outputCoverage = artemis::STDOUT;
            } else if (string(optarg).compare("none") == 0) {
                options.outputCoverage = artemis::NONE;
            } else {
                cerr << "ERROR: Invalid choice of coverage report " << optarg << endl;
                exit(1);
            }
            break;
        }

        case 'z': {
            if (string(optarg).compare("constant") == 0) {
                options.prioritizerStrategy = artemis::CONSTANT;
            } else if (string(optarg).compare("random") == 0) {
                options.prioritizerStrategy = artemis::RANDOM;
            } else if (string(optarg).compare("coverage") == 0) {
                options.prioritizerStrategy = artemis::COVERAGE;
            } else if (string(optarg).compare("readwrite") == 0) {
                options.prioritizerStrategy = artemis::READWRITE;
            } else if (string(optarg).compare("all") == 0){
                options.prioritizerStrategy = artemis::ALL_STRATEGIES;
            } else {
                cerr << "ERROR: Invalid choice of prioritizer strategy " << optarg << endl;
                exit(1);
            }

            break;
        }
         case 'v': {
            artemis::Log::addLogLevel(artemis::OFF);
         if(QString(optarg).indexOf("debug",0,Qt::CaseInsensitive)>=0){
                artemis::Log::addLogLevel(artemis::DEBUG);
            }

            if(QString(optarg).indexOf("warning",0,Qt::CaseInsensitive)>=0){
                artemis::Log::addLogLevel(artemis::WARNING);
            }
            if(QString(optarg).indexOf("error",0,Qt::CaseInsensitive)>=0){
                artemis::Log::addLogLevel(artemis::ERROR);
            }
            if(QString(optarg).indexOf("fatal",0,Qt::CaseInsensitive)>=0){
                artemis::Log::addLogLevel(artemis::FATAL);
            }

            if(QString(optarg).indexOf("all",0,Qt::CaseInsensitive)>=0){
                artemis::Log::addLogLevel(artemis::ALL);
            }

            if(QString(optarg).indexOf("off",0,Qt::CaseInsensitive)>=0){
                artemis::Log::addLogLevel(artemis::OFF);

            }

            break;
        }

        }
    }

    if (optind >= argc) {
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

void artemisConsoleMessageHandler(QtMsgType type, const char* msg)
{
    switch (type) {
    case QtDebugMsg:
        artemis::Log::debug(QString(msg).toStdString());
        break;
    case QtWarningMsg:
        artemis::Log::warning("Warning: "+QString(msg).toStdString());
        break;
    case QtCriticalMsg:
        artemis::Log::error("Critical: "+QString(msg).toStdString());
        break;
    case QtFatalMsg:
        artemis::Log::fatal("Fatal: "+QString(msg).toStdString());
        abort();
    }
}

int main(int argc, char* argv[])
{
    qInstallMsgHandler(artemisConsoleMessageHandler);

    ExceptionHandlingQApp app(argc, argv);

    artemis::Options options;
    QUrl url = parseCmd(argc, argv, options);

    artemis::ArtemisApplication artemisApp(0, &app, options, url);
    artemisApp.run(url);

    return app.exec();
}
