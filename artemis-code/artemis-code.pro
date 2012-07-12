TEMPLATE = app
TARGET = artemis
DEPENDPATH += .
INCLUDEPATH += ../WebKit/WebKitBuild/Release/include/ \
    ../WebKit/WebKitBuild/Release/include/QtWebKit/ \
    ../WebKit/Source/WebCore \
    . \
    inputgenerators \
    src
CONFIG -= app_bundle
OBJECTS_DIR = build
MOC_DIR = build
DESTDIR = dist
LIBS += ../WebKit/WebKitBuild/Release/lib/libQtWebKit.so
QMAKE_CXXFLAGS += -g \
    -DEXE_BUILD_DATE="`date +'\"%d-%m-%Y_%H:%M:%S\"'`"
DEFINES += ARTEMIS=1

installtarget.path = $$(ARTEMIS_PATH)/bin
installtarget.files = dist/*
INSTALLS += installtarget

# Input
HEADERS += src/runtime/input/ajaxinput.h \
    src/strategies/prioritizer/constantprioritizer.h \
    src/strategies/prioritizer/prioritizerstrategy.h \
    src/strategies/prioritizer/randomprioritizer.h \
    src/strategies/inputgenerator/targets/targetgenerator.h \
    src/builder/options.h \
    src/builder/builder.h \
    src/strategies/inputgenerator/variants/randomvariants.h \
    src/strategies/inputgenerator/variants/variantsgenerator.h \
    src/runtime/ajax/ajaxrequest.h \
    src/runtime/ajax/ajaxrequestlistener.h \
    src/runtime/browser/cookies/immutablecookiejar.h \
    src/runtime/events/baseeventparameters.h \
    src/runtime/events/domelementdescriptor.h \
    src/runtime/events/eventhandlerdescriptor.h \
    src/runtime/events/eventparameters.h \
    src/runtime/events/eventypes.h \
    src/runtime/events/forms/formfield.h \
    src/runtime/events/forms/formfieldtypes.h \
    src/runtime/events/forms/formfieldvalue.h \
    src/runtime/events/forms/forminput.h \
    src/runtime/events/keyboardeventparameters.h \
    src/runtime/events/mouseeventparameters.h \
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
    src/artemisapplication.h \
    src/artemisglobals.h \
    src/util/randomutil.h \
    src/coverage/codecoverage.h \
    src/coverage/lineinfo.h \
    src/coverage/coveragelistener.h \
    src/coverage/sourceinfo.h \
    src/coverage/coveragetooutputstream.h \
    src/urls/urlcollector.h \
    src/listeners/artemistopexecutionlistener.h \
    src/listeners/domstatesaverlistener.h \
    src/listeners/multiplexlistener.h \
    src/util/fileutil.h \
    src/util/urlutil.h \
    src/util/coverageutil.h \
    src/listeners/pagerecreatelistner.h \
    src/listeners/sourceloadinglistener.h \
    src/statistics/statsstorage.h \
    src/statistics/writers/pretty.h \
    src/exceptionhandlingqapp.h

SOURCES += src/runtime/input/ajaxinput.cpp \
    src/strategies/prioritizer/constantprioritizer.cpp \
    src/strategies/prioritizer/randomprioritizer.cpp \
    src/strategies/inputgenerator/targets/targetgenerator.cpp \
    src/builder/builder.cpp \
    src/strategies/inputgenerator/variants/randomvariants.cpp \
    src/runtime/ajax/ajaxrequest.cpp \
    src/runtime/ajax/ajaxrequestlistener.cpp \
    src/runtime/browser/cookies/immutablecookiejar.cpp \
    src/runtime/events/baseeventparameters.cpp \
    src/runtime/events/domelementdescriptor.cpp \
    src/runtime/events/eventhandlerdescriptor.cpp \
    src/runtime/events/eventtypes.cpp \
    src/runtime/events/forms/formfield.cpp \
    src/runtime/events/forms/formfieldvalue.cpp \
    src/runtime/events/forms/forminput.cpp \
    src/runtime/events/keyboardeventparameters.cpp \
    src/runtime/events/mouseeventparameters.cpp \
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
    src/artemis.cpp \
    src/artemisapplication.cpp \
    src/util/randomutil.cpp \
    src/coverage/codecoverage.cpp \
    src/coverage/lineinfo.cpp \
    src/coverage/coveragelistener.cpp \
    src/coverage/sourceinfo.cpp \
    src/coverage/coveragetooutputstream.cpp \
    src/urls/urlcollector.cpp \
    src/listeners/artemistopexecutionlistener.cpp \
    src/listeners/domstatesaverlistener.cpp \
    src/listeners/multiplexlistener.cpp \
    src/util/fileutil.cpp \
    src/util/urlutil.cpp \
    src/util/coverageutil.cpp \
    src/listeners/pagerecreatelistner.cpp \
    src/listeners/sourceloadinglistener.cpp \
    src/statistics/statsstorage.cpp \
    src/statistics/writers/pretty.cpp \
    src/exceptionhandlingqapp.cpp
QT += network
