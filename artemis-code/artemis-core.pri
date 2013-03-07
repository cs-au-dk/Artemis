
OBJECTS_DIR = build
MOC_DIR = build
DESTDIR = dist

QMAKE_CXXFLAGS += -g \
    -DEXE_BUILD_DATE="`date +'\"%d-%m-%Y_%H:%M:%S\"'`" \
    -Wno-unused-parameter

DEFINES += ARTEMIS=1

HEADERS += src/runtime/input/ajaxinput.h \
    src/strategies/prioritizer/constantprioritizer.h \
    src/strategies/prioritizer/prioritizerstrategy.h \
    src/strategies/prioritizer/randomprioritizer.h \
    src/strategies/inputgenerator/targets/targetgenerator.h \
    src/runtime/options.h \
    src/runtime/browser/ajax/ajaxrequest.h \
    src/runtime/browser/ajax/ajaxrequestlistener.h \
    src/runtime/browser/cookies/immutablecookiejar.h \
    src/runtime/input/events/baseeventparameters.h \
    src/runtime/input/events/domelementdescriptor.h \
    src/runtime/input/events/eventhandlerdescriptor.h \
    src/runtime/input/events/eventparameters.h \
    src/runtime/input/events/eventypes.h \
    src/runtime/input/forms/formfield.h \
    src/runtime/input/forms/formfieldtypes.h \
    src/runtime/input/forms/formfieldvalue.h \
    src/runtime/input/forms/forminput.h \
    src/runtime/input/events/keyboardeventparameters.h \
    src/runtime/input/events/mouseeventparameters.h \
    src/runtime/browser/artemiswebpage.h \
    src/runtime/executableconfiguration.h \
    src/runtime/input/baseinput.h \
    src/runtime/input/dominput.h \
    src/runtime/input/inputsequence.h \
    src/runtime/input/timerinput.h \
    src/runtime/browser/executionresult.h \
    src/runtime/browser/webkitexecutor.h \
    src/runtime/browser/timer.h \
    src/runtime/worklist/deterministicworklist.h \
    src/runtime/worklist/worklist.h \
    src/strategies/termination/numberofiterationstermination.h \
    src/strategies/termination/terminationstrategy.h \
    src/strategies/inputgenerator/inputgeneratorstrategy.h \
    src/strategies/inputgenerator/randominputgenerator.h \
    src/strategies/inputgenerator/targets/jquerylistener.h \
    src/strategies/inputgenerator/targets/jquerytarget.h \
    src/strategies/inputgenerator/targets/legacytarget.h \
    src/strategies/inputgenerator/targets/targetdescriptor.h \
    src/runtime/runtime.h \
    src/artemisglobals.h \
    src/util/randomutil.h \
    src/model/coverage/coveragelistener.h \
    src/model/coverage/sourceinfo.h \
    src/model/coverage/coveragetooutputstream.h \
    src/model/coverage/codeblockinfo.h \
    src/util/loggingutil.h \
    src/util/fileutil.h \
    src/util/urlutil.h \
    src/statistics/statsstorage.h \
    src/statistics/writers/pretty.h \
    src/exceptionhandlingqapp.h \
    src/runtime/browser/executionresultbuilder.h \
    src/strategies/inputgenerator/form/forminputgenerator.h \
    src/strategies/inputgenerator/form/staticforminputgenerator.h \
    src/strategies/inputgenerator/event/eventparametergenerator.h \
    src/strategies/inputgenerator/event/staticeventparametergenerator.h \
    src/strategies/inputgenerator/form/constantstringforminputgenerator.h \
    src/strategies/prioritizer/coverageprioritizer.h \
    src/runtime/appmodel.h \
    src/model/javascriptstatistics.h \
    src/strategies/prioritizer/readwriteprioritizer.h \
    src/strategies/prioritizer/collectedprioritizer.h \
    src/runtime/input/events/toucheventparameters.h

SOURCES += src/runtime/input/ajaxinput.cpp \
    src/strategies/prioritizer/constantprioritizer.cpp \
    src/strategies/prioritizer/randomprioritizer.cpp \
    src/strategies/inputgenerator/targets/targetgenerator.cpp \
    src/runtime/browser/ajax/ajaxrequest.cpp \
    src/runtime/browser/ajax/ajaxrequestlistener.cpp \
    src/runtime/browser/cookies/immutablecookiejar.cpp \
    src/runtime/input/events/baseeventparameters.cpp \
    src/runtime/input/events/domelementdescriptor.cpp \
    src/runtime/input/events/eventhandlerdescriptor.cpp \
    src/runtime/input/events/eventtypes.cpp \
    src/runtime/input/forms/formfield.cpp \
    src/runtime/input/forms/formfieldvalue.cpp \
    src/runtime/input/forms/forminput.cpp \
    src/runtime/input/events/keyboardeventparameters.cpp \
    src/runtime/input/events/mouseeventparameters.cpp \
    src/runtime/browser/artemiswebpage.cpp \
    src/runtime/executableconfiguration.cpp \
    src/runtime/input/dominput.cpp \
    src/runtime/input/inputsequence.cpp \
    src/runtime/input/timerinput.cpp \
    src/runtime/browser/executionresult.cpp \
    src/runtime/browser/webkitexecutor.cpp \
    src/runtime/browser/timer.cpp \
    src/runtime/worklist/deterministicworklist.cpp \
    src/strategies/termination/numberofiterationstermination.cpp \
    src/strategies/inputgenerator/randominputgenerator.cpp \
    src/strategies/inputgenerator/targets/jquerylistener.cpp \
    src/strategies/inputgenerator/targets/jquerytarget.cpp \
    src/strategies/inputgenerator/targets/legacytarget.cpp \
    src/strategies/inputgenerator/targets/targetdescriptor.cpp \
    src/runtime/runtime.cpp \
    src/util/loggingutil.cpp \
    src/util/randomutil.cpp \
    src/model/coverage/coveragelistener.cpp \
    src/model/coverage/sourceinfo.cpp \
    src/model/coverage/coveragetooutputstream.cpp \
    src/model/coverage/codeblockinfo.cpp \
    src/util/fileutil.cpp \
    src/util/urlutil.cpp \
    src/statistics/statsstorage.cpp \
    src/statistics/writers/pretty.cpp \
    src/exceptionhandlingqapp.cpp \
    src/runtime/browser/executionresultbuilder.cpp \
    src/strategies/inputgenerator/event/staticeventparametergenerator.cpp \
    src/strategies/inputgenerator/form/staticforminputgenerator.cpp \
    src/strategies/inputgenerator/form/constantstringforminputgenerator.cpp \
    src/strategies/prioritizer/coverageprioritizer.cpp \
    src/runtime/appmodel.cpp \
    src/model/javascriptstatistics.cpp \
    src/strategies/prioritizer/readwriteprioritizer.cpp \
    src/strategies/prioritizer/collectedprioritizer.cpp \
    src/runtime/input/events/toucheventparameters.cpp

QT += network
