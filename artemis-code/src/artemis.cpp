/*
 * Copyright 2012 Aarhus University
 *
 * Licensed under the GNU General Public License, Version 3 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *          http://www.gnu.org/licenses/gpl-3.0.html
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
#include "artemisglobals.h"
#include "runtime/input/forms/injectionvalue.h"
#include "util/useragents.h"

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
            "-f #<formElementId>=<formElementValue> : Set the form element with ID #<formElementId> to the value <formElementValue> at each iteration. Remember to write the # for the element ID.\n"
            "\n"
            "-F #<formElementId>=true|false : As with -f but for boolean value injections (e.g. into check boxes).\n"
            "\n"
            "-c <URl> : Cookies - // TODO\n"
            "\n"
            "-t <URL>:<PORT> : Set proxy\n"
            "\n"
            "-r       : set_recreate_page(true) // TODO\n"
            "\n"
            "-p       : dump_page_states(<path>) // TODO\n"
            "\n"
            "-s       : Enable DOM state checking\n"
            "\n"
            "-e       : Negate the last solved PC printed to stdout (used for testing)\n"
            "\n"
            "--major-mode <mode>:\n"
            "           The major-mode specifies the top-level test algorithm used by Artemis.\n"
            "\n"
            "           artemis - (default) the top-level test algorithm described in the ICSE'11 Artemis paper\n"
            "           manual - open a browser window for manual testing of web applications\n"
            "           concolic - perform an automated concolic analysis of form validation code\n"
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
            "--coverage-report-ignore <URL>:\n"
            "           Exclude the given URL from the coverage report and coverage statistics.\n"
            "\n"
            "--path-trace-report <report-type>:\n"
            "           Output a report of the execution path through the covered JavaScript.\n"
            "\n"
            "           all - All executed paths are displayed\n"
            "           click - Only paths beginning with a click event are displayed\n"
            "           none - (default) Path trace report is omitted\n"
            "           html - HTML trace report is generated in the folder you run Artemis from\n"
            "\n"
            "--concolic-button <XPath>:\n"
            "           Use the given XPath to locate the button to be used in concolic mode.\n"
            "           If not supplied, the concolic mode will use its built-in button finding, which is not robust.\n"
            "\n"
            "--concolic-tree-output <trees>:\n"
            "           none - Do not output any graphs.\n"
            "           final (default) - Generate a graph of the final tree after analysis.\n"
            "           final-overview - Like final but also includes a simplified overview graph.\n"
            "           all - Generate a graph of the tree at every iteration.\n"
            "           all-overview - Like all but also includes simplified overview graphs.\n"
            "\n"
            "--concolic-dfs-depth <n>x<m>\n"
            "           The depth limit used for the iterative depth-first search.\n"
            "           n is the base depth limit (of symbolic branches).\n"
            "           m is the number of passes of the search, each at a lower depth.\n"
            "           The default is 5x3 for a total depth limit of 15 after two restarts.\n"
            "\n"
            "--concolic-unlimited-depth\n"
            "           Removes the restart limit from the concolic depth-first search procedure.\n"
            "\n"
            "--concolic-event-sequences <strategy>\n"
            "           ignore (default) - Ignore handlers for individual field modification.\n"
            "           simple - Fire the onchange event for each field which is injected.\n"
            "\n"
            "--smt-solver <solver>:\n"
            "           z3str - Use the Z3-str SMT solver as backend.\n"
            "           cvc4 (default) - Use the CVC4 SMT solver as backend. CVC4 is required to be on your path.\n"
            "           kaluza - Use the Kaluza solver as backend.\n"
            "\n"
            "--strategy-priority <strategy>:\n"
            "           Select priority strategy.\n"
            "\n"
            "           constant - (default) assign the same priority to new configurations\n"
            "           random - assign a random priority to new configurations\n"
            "           coverage - assign higher priority to configurations with low coverage\n"
            "           readwrite - use read/write-sets for JavaScript properties to assign priorities\n"
            "           all - a combination of the constant, the coverage and the readwrite strategy, as defined in the Artemis article\n"
            "\n"
            "--export-event-sequence <output type> :\n"
            "           selenium - Will create a selenium test suite of all the iterations.\n"
            "           json - Will create a JSON file containing the iterations.\n"
            "\n"
            "--input-strategy-same-length <num>:\n"
            "           Set the number of permutations of an executed sequence (of same length) generated by the input generator.\n"
            "\n"
            "--function-call-heap-report <report-type>\n"
            "           Writes a report containing heaps before all or named functioncalls.\n"
            "\n"
            "           all - All calls are reported\n"
            "           named - Only named calls are reported\n"
            "           none - (default) No calls are reported\n"
            "\n"
            "--function-call-heap-report-random-factor <int>\n"
            "           When faced with many function calls, this parameter saves data with a factor <int>^-1\n"
            "\n"
            "--user-agent <custom-ua>\n"
            "           Change the user-agent reported by Artemis to <custom-ua>.\n"
            "           The following built-in user agents can also be specified (case sensitive):\n"
            "           default, iphone4, ipad4, nexus5, chrome35\n"
            "\n";

    struct option long_options[] = {
    {"strategy-form-input-generation", required_argument, NULL, 'x'},
    {"coverage-report", required_argument, NULL, 'y'},
    {"strategy-priority", required_argument, NULL, 'z'},
    {"input-strategy-same-length", required_argument, NULL, 'j'},
    {"coverage-report-ignore", required_argument, NULL, 'k'},
    {"major-mode", required_argument, NULL, 'm'},
    {"path-trace-report", required_argument, NULL, 'a'},
    {"function-call-heap-report", required_argument, NULL, 'g'},
    {"function-call-heap-report-random-factor", required_argument, NULL, 'l'},
    {"concolic-tree-output", required_argument, NULL, 'd'},
    {"concolic-button", required_argument, NULL, 'b'},
    {"concolic-dfs-depth", required_argument, NULL, 'D'},
    {"concolic-unlimited-depth", no_argument, NULL, 'u'},
    {"concolic-event-sequences", required_argument, NULL, 'w'},
    {"smt-solver", required_argument, NULL, 'n'},
    {"export-event-sequence", required_argument, NULL, 'o'},
    {"help", no_argument, NULL, 'h'},
    {"option-values", optional_argument, NULL, 'q'},
    {"user-agent", required_argument, NULL, 'U'},
    {0, 0, 0, 0}
    };

    int option_index = 0;
    char c;
    artemis::Log::addLogLevel(artemis::INFO);
    artemis::Log::addLogLevel(artemis::FATAL);

    while ((c = getopt_long(argc, argv, "ehsrp:a:m:I:F:f:t:c:i:v:", long_options, &option_index)) != -1) {

        switch (c) {

        case 'a': {

            if (string(optarg).compare("all") == 0) {
                options.reportPathTrace  = artemis::ALL_TRACES;
            } else if (string(optarg).compare("click") == 0) {
                options.reportPathTrace = artemis::CLICK_TRACES;
            } else if (string(optarg).compare("none") == 0) {
                options.reportPathTrace = artemis::NO_TRACES;
            }else if (string(optarg).compare("html") == 0) {
                options.reportPathTrace = artemis::HTML_TRACES;
            } else {
                cerr << "ERROR: Invalid choice of path-trace-report " << optarg << endl;
                exit(1);
            }

            break;
        }

        case 'b': {
            options.concolicEntryPoint = QString(optarg);
            break;
        }

        case 'c': {
            QStringList parts = QString(optarg).split("=");
            options.presetCookies.insert(parts.at(0), parts.at(1));
            break;
        }

        case 'd': {

            if (string(optarg).compare("none") == 0) {
                options.concolicTreeOutput = artemis::TREE_NONE;
            } else if (string(optarg).compare("final") == 0) {
                options.concolicTreeOutput = artemis::TREE_FINAL;
            } else if (string(optarg).compare("all") == 0) {
                options.concolicTreeOutput = artemis::TREE_ALL;
            } else if (string(optarg).compare("final-overview") == 0) {
                options.concolicTreeOutput = artemis::TREE_FINAL;
                options.concolicTreeOutputOverview = true;
            } else if (string(optarg).compare("all-overview") == 0) {
                options.concolicTreeOutput = artemis::TREE_ALL;
                options.concolicTreeOutputOverview = true;
            } else {
                cerr << "ERROR: Invalid choice of concolic-tree-output " << optarg << endl;
                exit(1);
            }

            break;
        }

        case 'D': {
            QStringList parts = QString(optarg).split("x");
            if(parts.length() != 2) {
                cerr << "ERROR: Invalid format for concolic-dfs-depth " << optarg << endl;
                exit(1);
            }

            bool ok1, ok2;
            int depth = parts[0].toInt(&ok1);
            int passes = parts[1].toInt(&ok2);
            if(!ok1 || !ok2 || depth < 1 || passes < 1) {
                cerr << "ERROR: Invalid value for concolic-dfs-depth " << optarg << endl;
                exit(1);
            }

            options.concolicDfsDepthLimit = depth;
            options.concolicDfsRestartLimit = passes;

            break;
        }

        case 'e': {
            options.concolicNegateLastConstraint = true;

            break;
        }

        case 'f': {

            QString input = QString(optarg);

            int lastEqualsIndex = QString(optarg).lastIndexOf("=");
            Q_ASSERT(lastEqualsIndex >= 0);

            options.presetFormfields.insert(input.left(lastEqualsIndex), artemis::InjectionValue(input.mid(lastEqualsIndex+1)));
            break;
        }

        case 'F': {
            // Boolean injected value

            QString input = QString(optarg);

            int lastEqualsIndex = QString(optarg).lastIndexOf("=");
            Q_ASSERT(lastEqualsIndex >= 0);

            QString name = input.left(lastEqualsIndex);
            QString value = input.mid(lastEqualsIndex+1);

            if (value == "true") {
                options.presetFormfields.insert(name, artemis::InjectionValue(true));
            } else if (value == "false") {
                options.presetFormfields.insert(name, artemis::InjectionValue(false));
            }else {
                cerr << "ERROR: Invalid choice of injection " << name.toStdString() << "=" << value.toStdString() << endl;
                cerr << "Should be 'true' or 'false' only for boolean injections." << endl;
                exit(1);
            }
            break;
        }

        case 'I': {
            // Integer injected value

            QString input = QString(optarg);

            int lastEqualsIndex = QString(optarg).lastIndexOf("=");
            Q_ASSERT(lastEqualsIndex >= 0);

            QString name = input.left(lastEqualsIndex);
            QString value = input.mid(lastEqualsIndex+1);

            bool ok;
            int v = value.toInt(&ok);

            options.presetFormfields.insert(name, artemis::InjectionValue(v));

            if (!ok) {
                cerr << "ERROR: Invalid choice of injection " << name.toStdString() << "=" << value.toStdString() << endl;
                cerr << "Should be a valid integer for integer injections." << endl;
                exit(1);
            }

            break;
        }

        case 'g' : {
            if(string(optarg).compare("all") == 0){
                options.reportHeap = artemis::ALL_CALLS;
            } else if (string(optarg).compare("named") == 0){
                options.reportHeap = artemis::NAMED_CALLS;
            } else if (string(optarg).compare("none") == 0){

            } else {
                cerr << "ERROR: Invalid choice of function-call-heap-report " << optarg << endl;
                exit(1);
            }
            break;
        }

        case 'h': {
            std::cout << usage;
            exit(0);
        }

        case 'i': {
            options.iterationLimit = QString(optarg).toInt();
            break;
        }

        case 'j': {
            options.numberSameLength = QString(optarg).toInt();
            break;
        }

        case 'k': {
            options.coverageIgnoreUrls.insert(QUrl(QString(optarg)));
            break;
        }

        case 'l' : {
            options.heapReportFactor = std::max(QString(optarg).toInt(), 1);
            break;
        }

        case 'm': {

            if (string(optarg).compare("artemis") == 0) {
                options.majorMode = artemis::AUTOMATED;
            } else if (string(optarg).compare("manual") == 0) {
                options.majorMode = artemis::MANUAL;
            } else if (string(optarg).compare("concolic") == 0) {
                options.majorMode = artemis::CONCOLIC;
            } else {
                cerr << "ERROR: Invalid choice of major-mode " << optarg << endl;
                exit(1);
            }

            break;
        }

        case 'n': {

            if (string(optarg).compare("kaluza") == 0) {
                options.solver = artemis::KALUZA;
            } else if (string(optarg).compare("z3str") == 0) {
                options.solver = artemis::Z3STR;
            } else if (string(optarg).compare("cvc4") == 0) {
                options.solver = artemis::CVC4;
            } else {
                cerr << "ERROR: Invalid choice of --smt-solver " << optarg << endl;
                exit(1);
            }

            break;
        }

        case 'o':{
            if(string(optarg).compare("selenium") == 0){
                options.exportEventSequence = artemis::EXPORT_SELENIUM;
            } else if(string(optarg).compare("json") == 0){
                options.exportEventSequence = artemis::EXPORT_JSON;
            } else {
                cerr << "ERROR: Invalid choice of export-event-sequnce " << optarg << endl;
                exit(1);
            }
            break;
        }


        case 'p': {
            QDir ld = QDir(QString(optarg));
            options.dumpPageStates = "k";
            break;
        }



        case 'q': {
            if(optarg){
                if(string(optarg).compare("--major-mode") == 0){
                    std::cout << "artemis manual concolic";
                } else if(string(optarg).compare("--strategy-form-input-generation") == 0){
                    std::cout << "javascript-constants random";
                } else if(string(optarg).compare("--coverage-report") == 0){
                    std::cout << "html stdout none";
                } else if(string(optarg).compare("--path-trace-report") == 0){
                    std::cout << "all click html none";
                } else if(string(optarg).compare("--concolic-tree-output") == 0){
                    std::cout << "none final all final-overview all-overview";
                } else if(string(optarg).compare("--concolic-event-sequences") == 0){
                    std::cout << "ignore simple";
                }else if(string(optarg).compare("--strategy-priority") == 0){
                    std::cout << "constant random coverage readwrite all";
                } else if(string(optarg).compare("--export-event-sequence") == 0){
                    std::cout << "selenium json";
                } else if(string(optarg).compare("--function-call-heap-report") == 0){
                    std::cout << "all named none";
                } else if(string(optarg).compare("--smt-solver") == 0){
                    std::cout << "z3str cvc4 kaluza";
                } else if(string(optarg).compare("--export-event-sequence") == 0){
                    std::cout << "selenium";
                }

            } else {
                std::cout << "-c -t -r -p -s -e -i --major-mode "
                             "--strategy-form-input-generation "
                             "--coverage-report "
                             "--coverage-report-ignore "
                             "--path-trace-report "
                             "--concolic-button "
                             "--concolic-tree-output "
                             "--concolic-unlimited-depth "
                             "--concolic-event-sequences "
                             "--strategy-priority "
                             "--smt-solver "
                             "--export-event-sequence "
                             "--input-strategy-same-length "
                             "--function-call-heap-report "
                             "--function-call-heap-report-random-factor "
                             "--export-event-sequence";
            }

            exit(0);
        }


        case 'r': {
            options.recreatePage = true;
            break;
        }

        case 's': {
            options.disableStateCheck = false;
            break;
        }

        case 't': {
            options.useProxy = QString(optarg);
            break;
        }

        case 'u': {
            options.concolicDfsRestartLimit = 0;
            break;
        }

        case 'U': {
            if(artemis::UserAgents::userAgents().contains(QString(optarg))) {
                options.customUserAgent = artemis::UserAgents::userAgents().value(QString(optarg));
            } else {
                options.customUserAgent = QString(optarg);
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

           if(QString(optarg).indexOf("info",0,Qt::CaseInsensitive)>=0){
               artemis::Log::addLogLevel(artemis::INFO);
           }

           break;
       }

        case 'w': {
            if (string(optarg).compare("ignore") == 0) {
                options.concolicTriggerEventHandlers = false;
            } else if (string(optarg).compare("simple") == 0) {
                options.concolicTriggerEventHandlers = true;
            } else {
                cerr << "ERROR: Invalid choice of event-sequence handling strategy " << optarg << endl;
                exit(1);
            }

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
            if (QString(optarg).toLower().compare("html") == 0) {
                options.outputCoverage = artemis::HTML;
            } else if (QString(optarg).toLower().compare("stdout") == 0) {
                options.outputCoverage = artemis::STDOUT;
            } else if (QString(optarg).toLower().compare("none") == 0) {
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

        }
    }

    QUrl url;

    if (optind >= argc) {
        // If we are in manual mode then the url is optional.
        if(options.majorMode != artemis::MANUAL){
            cerr << "Error: You must specify a URL" << endl;
            exit(1);
        }else{
            url = artemis::examplesIndexUrl();
        }

    }else{

        QStringList rawurl = QString(argv[optind]).split("@");
        url = rawurl.last();

        if (options.useProxy.length() > 0 && url.host() == "localhost") {
            cerr << "Error: You can not use the proxy setting in Artemis for content hosted on localhost" << endl;
            exit(1);
        }

        if (url.scheme().isEmpty()) {
            QFile file(url.toString());

            if (!file.exists()) {
                // the http:// part is missing and it is not a file
                url = QUrl("http://" + url.toString());
            }
        }

        if (!url.isValid()) {
            cerr << "Error: The URL " << url.toString().toStdString() << " is not valid" << endl;
            exit(1);
        }

        if (rawurl.size() > 1) {
            QStringList rawauth = rawurl.first().split(":");
            url.setUserName(rawauth.first());
            url.setPassword(rawauth.last());
        }

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
