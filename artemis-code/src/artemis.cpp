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

#include "JavaScriptCore/symbolic/symbolicinterpreter.h"

using namespace std;

artemis::ConcolicSearchSelector getSelector(QString concolicSelectionProcedure);


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
            "-c <KEY=VALUE> : Set a cookie value for the global domain.\n"
            "\n"
            "-t <URL>:<PORT> : Set proxy\n"
            "\n"
            "-s       : Enable DOM state checking\n"
            "\n"
            "-e       : Negate the last solved PC printed to stdout (used for testing)\n"
            "\n"
            "--debug-concolic: Run the concolic subsystem on the last iteration and output results.\n"
            "\n"
            "--major-mode <mode>:\n"
            "           The major-mode specifies the top-level test algorithm used by Artemis.\n"
            "\n"
            "           artemis - (default) the top-level test algorithm described in the ICSE'11 Artemis paper\n"
            "           manual - open a browser window for manual testing of web applications\n"
            "           concolic - perform an automated concolic analysis of form validation code\n"
            "           concolic-test - perform a concolic analysis of standalone JavaScript snippets (for testing)\n"
            "           server - provides an API to control the Artemis browser and report information\n"
            "\n"
            "--strategy-form-input-generation <strategy>:\n"
            "           Select form input generation strategy.\n"
            "\n"
            "           javascript-constants - select form inputs based in observed JavaScript constants\n"
            "           random - (default) random inputs\n"
            "\n"
            "\n"
            "--strategy-target-selection <strategy>:\n"
            "           Select target selection strategy.\n"
            "\n"
            "           concolic - use concolic testing to select a target\n"
            "           jquery - use a model to support instrumented jQuery\n"
            "           legacy - (default) set the target to the element on which the event-handler is registered\n"
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
            "--strategy-event-generation <strategy>:\n"
            "           Select event-sequence generation strategy.\n"
            "\n"
            "           random-incremental - (default) permutates the latest event or extends event sequence with one new event\n"
            "           fasttrack - generate one large event-sequence of all known events (forces -i 2) \n"
            "\n"
            "--event-visibility-check <true|false>:\n"
            "           Enable or disable event visibility checks, which filters out any event which is not attached to a user visible element. Default: (false).\n"
            "\n"
            "--input-strategy-same-length <num>:\n"
            "           Set the number of permutations of an executed sequence (of same length) generated by the input generator.\n"
            "\n"
            "--load-new-urls <true|false>:\n"
            "           Whether URLs should be loaded (e.g. after clicking a link) in major-mode 'artemis'. Default: false.\n"
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
            "--concolic-search-procedure <search>\n"
            "           Choose the search procedure used to choose new areas of the concolic execution tree to explore.\n"
            "\n"
            "           dfs - (default) Depth first search with iterative deepening\n"
            "           selector - Use the selectors system (see concolic-selection-procedure and concolic-selection-budget)\n"
            "\n"
            "--concolic-dfs-depth <n>x<m>\n"
            "           The depth limit used for the iterative depth-first search.\n"
            "           n is the base depth limit (of symbolic branches).\n"
            "           m is the number of passes of the search, each at a lower depth.\n"
            "           The default is 5x3 for a total depth limit of 15 after two restarts.\n"
            "\n"
            "--concolic-dfs-unlimited-depth\n"
            "           Removes the restart limit from the concolic depth-first search procedure.\n"
            "\n"
            "--concolic-selection-procedure <selector>\n"
            "           The procedure used to select the next exploration when concolic-search-procedure is set to selectors.\n"
            "\n"
            "           dfs - (default) Depth first search (no depth limit)\n"
            "           random - choose new explorations at random\n"
            "           avoid-unsat - experimental procedure which chooses branches with less history of being unsatisfiable\n"
            "           round-robin(<s1>:<s2>:...:<sN>) - comines other selectors\n"
            "\n"
            "--concolic-selection-budget <n>\n"
            "           The number of times the selection procedures will attempt new exploration.\n"
            "           The default is 25. Select 0 for unlimited attempts.\n"
            "\n"
            "--concolic-event-sequences <strategy>\n"
            "           ignore (default) - Ignore handlers for individual field modification.\n"
            "           simple - Fire the onchange event for each field which is injected.\n"
            "\n"
            "--concolic-event-sequence-permutation <permutation>\n"
            "           In the 'simple' mode of concolic-event-sequences, each event handler is\n"
            "           triggered in the DOM order bey default and this option allows the order to be\n"
            "           modified. The new order is a reordering of the default list [1,2,...,N]\n"
            "           where N is the number of event handlers. e.g. if there are 4 fields then a\n"
            "           valid value would be [4,2,1,3].\n"
            "           It is also possible to remove handlers from the event sequence, e.g. [1,2,4]\n"
            "\n"
            "--concolic-event-handler-report\n"
            "           Outputs a graph of the symbolic variables which are read from each event handler.\n"
            "           (Requires major-mode concolic and concolic-event-sequences)\n"
            "\n"
            "--concolic-disable-features <features-list>\n"
            "           Used for benchmarking only. Disables the listed features (comma separated list).\n"
            "           The features which can be disabled with this option are:\n"
            "           radio-restriction, select-restriction, select-restriction-dynamic, select-symbolic-index,\n"
            "           select-link-value-index, select-indirection-option-index, radio-checkbox-symbolic,\n"
            "           concrete-value-property, symbolic-after-injection, cvc4-coercion-opt,\n"
            "           event-sequence-sync-injections\n"
            "\n"
            "--concolic-test-mode-js <js-file>\n"
            "           Specifies the JavaScript source file to be used by major-mode concolic-test.\n"
            "\n"
            "--smt-solver <solver>:\n"
            "           z3str - Use the Z3-str SMT solver as backend.\n"
            "           cvc4 (default) - Use the CVC4 SMT solver as backend.\n"
            "           kaluza - Use the Kaluza solver as backend.\n"
            "\n"
            "--export-event-sequence <output type> :\n"
            "           selenium - Will create a selenium test suite of all the iterations.\n"
            "           json - Will create a JSON file containing the iterations.\n"
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
            "\n"
            "--analysis-server-port <port>\n"
            "           The port the analysis server major-mode will listen on (default 8008).\n"
            "\n"
            "--analysis-server-debug-view\n"
            "           The analysis server will display a (non-interactive) window showing the internal browser.\n"
            "\n"
            "--analysis-server-log\n"
            "           The analysis server will dump a log of all commands and responses.\n"
            "\n"
            "--testing-concolic-send-iteration-count-to-server\n"
            "           Only used as part of our test suite. Adds a query of ArtemisIteration=X to each URL in concolic mode.\n"
            "\n"
            "--event-delegation-testing\n"
            "           Used during development to test the event delegation support (i.e. strategy-target-selection 'concolic'). Restricts Artemis to only test event sequences of length 1. [Works with major-mode 'artemis' and strategy-event-generation 'random-incremental' (both default).]\n"
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
    {"concolic-search-procedure", required_argument, NULL, 'S'},
    {"concolic-dfs-unlimited-depth", no_argument, NULL, 'u'},
    {"concolic-selection-procedure", required_argument, NULL, 'T'},
    {"concolic-selection-budget", required_argument, NULL, 'R'},
    {"concolic-event-sequences", required_argument, NULL, 'w'},
    {"concolic-event-sequence-permutation", required_argument, NULL, 'W'},
    {"concolic-event-handler-report", no_argument, NULL, 'H'},
    {"smt-solver", required_argument, NULL, 'n'},
    {"export-event-sequence", required_argument, NULL, 'o'},
    {"help", no_argument, NULL, 'h'},
    {"option-values", optional_argument, NULL, 'q'},
    {"user-agent", required_argument, NULL, 'U'},
    {"strategy-target-selection", required_argument, NULL, 'A'},
    {"concolic-disable-features", required_argument, NULL, 'B'},
    {"strategy-event-generation", required_argument, NULL, 'C'},
    {"concolic-dfs-depth", required_argument, NULL, 'D'},
    {"debug-concolic", no_argument, NULL, 'E'},
    {"event-visibility-check", required_argument, NULL, 'G'},
    {"analysis-server-port", required_argument, NULL, 'p'},
    {"analysis-server-debug-view", no_argument, NULL, 'V'},
    {"analysis-server-log", no_argument, NULL, 'K'},
    {"load-new-urls", required_argument, NULL, 'L'},
    {"concolic-test-mode-js", required_argument, NULL, 'J'},
    {"testing-concolic-send-iteration-count-to-server", no_argument, NULL, 'M'},
    {"event-delegation-testing", no_argument, NULL, 'N'},
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

        case 'B': {
            QStringList features = QString(optarg).split(",");
            foreach(QString feature, features) {
                feature = feature.trimmed();
                if (feature == "radio-restriction") {
                    options.concolicDisabledFeatures |= artemis::RADIO_RESTRICTION;
                } else if (feature == "select-restriction") {
                    options.concolicDisabledFeatures |= artemis::SELECT_RESTRICTION;
                } else if (feature == "select-restriction-dynamic") {
                    options.concolicDisabledFeatures |= artemis::SELECT_RESTRICTION_DYNAMIC;
                } else if (feature == "select-link-value-index") {
                    options.concolicDisabledFeatures |= artemis::SELECT_LINK_VALUE_INDEX;
                } else if (feature == "cvc4-coercion-opt") {
                    options.concolicDisabledFeatures |= artemis::CVC4_COERCION_OPT;
                } else if (feature == "select-indirection-option-index") {
                    Symbolic::SymbolicInterpreter::setFeatureIndirectOptionIndexLookupEnabled(false);
                } else if (feature == "select-symbolic-index") {
                    Symbolic::SymbolicInterpreter::setFeatureSymbolicSelectedIndexEnabled(false);
                } else if (feature == "radio-checkbox-symbolic") {
                    Symbolic::SymbolicInterpreter::setFeatureSymbolicCheckedPropertyEnabled(false);
                } else if (feature == "concrete-value-property") {
                    options.concolicDisabledFeatures |= artemis::CONCRETE_VALUE_PROPERTY;
                    Symbolic::SymbolicInterpreter::setFeatureConcreteValuePropertyEnabled(false);
                } else if (feature == "symbolic-after-injection") {
                    Symbolic::SymbolicInterpreter::setFeatureSymbolicTriggeringEnabled(false);
                } else if (feature == "event-sequence-sync-injections") {
                    options.concolicDisabledFeatures |= artemis::EVENT_SEQUENCE_SYNC_INJECTIONS;
                } else {
                    cerr << "ERROR: Invalid choice of concolic-disable-features " << optarg << endl;
                    exit(1);
                }
            }
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

        case 'H': {
            options.concolicEventHandlerReport = true;
            break;
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

        case 'K': {
            options.analysisServerLog = true;
            break;
        }

        case 'l' : {
            options.heapReportFactor = std::max(QString(optarg).toInt(), 1);
            break;
        }

        case 'L': {
            if (string(optarg).compare("true") == 0) {
                options.artemisLoadUrls = true;
            } else if (string(optarg).compare("false") == 0) {
                options.artemisLoadUrls = false;
            } else {
                cerr << "ERROR: Invalid choice of load-new-urls " << optarg << endl;
                exit(1);
            }
            break;
        }

        case 'm': {

            if (string(optarg).compare("artemis") == 0) {
                options.majorMode = artemis::AUTOMATED;
            } else if (string(optarg).compare("manual") == 0) {
                options.majorMode = artemis::MANUAL;
                options.saveCookiesForSession = true;
            } else if (string(optarg).compare("concolic") == 0) {
                options.majorMode = artemis::CONCOLIC;
            } else if (string(optarg).compare("server") == 0) {
                options.majorMode = artemis::ANALYSIS_SERVER;
                options.saveCookiesForSession = true;
            } else if (string(optarg).compare("concolic-test") == 0) {
                options.majorMode = artemis::CONCOLIC_TEST;
            } else {
                cerr << "ERROR: Invalid choice of major-mode " << optarg << endl;
                exit(1);
            }

            break;
        }

        case 'M': {
            options.testingConcolicSendIterationCountToServer = true;
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

        case 'N': {
            options.delegationTestingMode = true;
            break;
        }

        case 'o': {
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
            bool ok;
            options.analysisServerPort = QString(optarg).toUShort(&ok);
            if(!ok) {
                cerr << "ERROR: Invalid choice of analysis-server-port " << optarg << endl;
                exit(1);
            }
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
                } else if(string(optarg).compare("----concolic-search-procedure") == 0){
                    std::cout << "dfs dfs-testing random easily-bored";
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
                             "--concolic-search-procedure "
                             "--concolic-dfs-depth "
                             "--concolic-dfs-unlimited-depth "
                             "--concolic-selection-procedure "
                             "--concolic-selection-budget "
                             "--concolic-event-sequences "
                             "--strategy-priority "
                             "--smt-solver "
                             "--export-event-sequence "
                             "--input-strategy-same-length "
                             "--function-call-heap-report "
                             "--function-call-heap-report-random-factor "
                             "--export-event-sequence "
                             "--analysis-server-port ";
            }

            exit(0);
        }

        case 'R': {
            bool ok;
            options.concolicSearchBudget = QString(optarg).toUInt(&ok);
            if(!ok) {
                cerr << "ERROR: Invalid choice of concolic-search-budget " << optarg << endl;
                exit(1);
            }
            break;
        }

        case 's': {
            options.disableStateCheck = false;
            break;
        }

        case 'S': {
            if(string(optarg).compare("dfs") == 0){
                options.concolicSearchProcedure = artemis::SEARCH_DFS;
            } else if(string(optarg).compare("selector") == 0){
                options.concolicSearchProcedure = artemis::SEARCH_SELECTOR;
            } else {
                std::cerr << "ERROR: Invalid choice of concolic-search-procedure " << optarg << std::endl;
                exit(1);
            }
            break;
        }

        case 't': {
            options.useProxy = QString(optarg);
            break;
        }

        case 'T': {
            // getSelector will exit with an error message itself if necesary.
            //std::cerr << optarg << std::endl;
            options.concolicSearchSelector = getSelector(QString(optarg));
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

        case 'V': {
            options.analysisServerDebugView = true;
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

        case 'W': {
            // Validity is checked when used in the concolic runtime.
            options.concolicEventHandlerPermutation = QString(optarg);

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

        case 'A': {

            if (string(optarg).compare("jquery") == 0) {
                options.targetStrategy = artemis::TARGET_JQUERY;
            } else if (string(optarg).compare("concolic") == 0) {
                options.targetStrategy = artemis::TARGET_CONCOLIC;
            } else if (string(optarg).compare("legacy") == 0) {
                options.targetStrategy = artemis::TARGET_LEGACY;
            } else {
                cerr << "ERROR: Invalid choice of target strategy " << optarg << endl;
                exit(1);
            }

            break;

        }

        case 'C': {

            if (string(optarg).compare("random-incremental") == 0) {
                options.eventGenerationStrategy = artemis::EVENT_LEGACY;
            } else if (string(optarg).compare("fasttrack") == 0) {
                options.eventGenerationStrategy = artemis::EVENT_FASTTRACK;
            } else {
                cerr << "ERROR: Invalid choice of event generation strategy " << optarg << endl;
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
            unsigned int depth = parts[0].toUInt(&ok1);
            unsigned int passes = parts[1].toUInt(&ok2);
            if(!ok1 || !ok2 || depth < 1 || passes < 1) {
                cerr << "ERROR: Invalid value for concolic-dfs-depth " << optarg << endl;
                exit(1);
            }

            options.concolicDfsDepthLimit = depth;
            options.concolicDfsRestartLimit = passes;

            break;
        }

        case 'E': {
            options.debugConcolic = true;

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

        case 'G': {

            if (string(optarg).compare("true") == 0) {
                options.enableEventVisibilityFiltering = true;
            } else if (string(optarg).compare("false") == 0) {
                options.enableEventVisibilityFiltering = false;
            } else {
                cerr << "ERROR: Invalid choice of event visibility filtering " << optarg << endl;
                exit(1);
            }

            break;
        }

        case 'J': {
            // Validity is checked when used in the concolic-standalone runtime.
            options.concolicTestModeJsFile = QString(optarg);
            break;
        }

        case '?': {
            // getopt has already printed an error
            exit(1);
        }

        default: {
            cerr << "Unhandled option." << endl;
            exit(1);
        }

        }
    }

    // special rules

    if (options.eventGenerationStrategy == artemis::EVENT_FASTTRACK) {
        options.iterationLimit = 2; // anything else does not make sense
    }

    // url handling

    QUrl url;

    if (optind >= argc) {
        // Major-mode concolic-test does not use a URL.
        if (options.majorMode == artemis::CONCOLIC_TEST) {
            url = QUrl("about:blank");
        } else if (options.majorMode == artemis::MANUAL) { // If we are in manual mode then the url is optional.
            url = artemis::examplesIndexUrl();
        } else if (options.majorMode == artemis::ANALYSIS_SERVER) { // If we are in server mode then the URL is optional.
            url = QUrl("about:blank");
        } else {
            // In all other cases, a URL is required.
            cerr << "Error: You must specify a URL" << endl;
            exit(1);
        }

    }else{
        // Major-mode concolic-test does not use a URL.
        if (options.majorMode == artemis::CONCOLIC_TEST) {
            cerr << "Error: Major-mode concolic-test does not use a URL." << endl;
            exit(1);
        }

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

    QStringList allArguments;
    for (int i = 0; i < argc; i++) {
        allArguments.append(argv[i]);
    }
    options.allArguments = allArguments.join(" ");

    return url;
}

/**
 *  Parses the argument to concolic-selection-procedure into a new ConcolicSearchSelector struct.
 */
artemis::ConcolicSearchSelector getSelector(QString concolicSelectionProcedure) {
    //std::cerr << concolicSelectionProcedure.toStdString() << std::endl;
    //std::cerr << concolicSelectionProcedure.startsWith("round-robin") << std::endl;

    QRegExp delimitXXX("[()]");
    //qDebug() << concolicSelectionProcedure.section(delimitXXX,1,1).split(":");

    artemis::ConcolicSearchSelector selector;
     if (concolicSelectionProcedure.compare("dfs") == 0)
     {
         selector.type = artemis::ConcolicSearchSelector::SELECTOR_DFS;
     }
     else if (concolicSelectionProcedure.compare("random") == 0)
     {
         selector.type = artemis::ConcolicSearchSelector::SELECTOR_RANDOM;
     }
     else if (concolicSelectionProcedure.compare("avoid-unsat") == 0)
     {
         selector.type = artemis::ConcolicSearchSelector::SELECTOR_AVOID_UNSAT;
     }
     else if (concolicSelectionProcedure.startsWith("round-robin"))
     {
         selector.type = artemis::ConcolicSearchSelector::SELECTOR_ROUND_ROBIN;
         QRegExp delimit("[()]");
         QStringList parts = concolicSelectionProcedure.section(delimit,1,1).split(":");
         for (int i = 0; i < parts.size(); i++)
         {
             selector.components.append(getSelector(parts.at(i)));
         }
     }
     else
     {
         std::cerr << "ERROR: Invalid choice of concolic-selection-procedure: " << concolicSelectionProcedure.toStdString() << std::endl;
         exit(1);
     }
     return selector;
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
