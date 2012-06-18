TEMPLATE = app
TARGET = artemis
DEPENDPATH += .
INCLUDEPATH += ../WebKit/WebKitBuild/Debug/include/ \
    ../WebKit/WebKitBuild/Debug/include/QtWebKit/ \
    ../WebKit/Source/WebCore \
    . \
    inputgenerators \
    src
CONFIG -= app_bundle
OBJECTS_DIR = build
MOC_DIR = build
DESTDIR = dist
LIBS += ../WebKit/WebKitBuild/Debug/lib/libQtWebKit.so
QMAKE_CXXFLAGS += -g \
    -DEXE_BUILD_DATE="`date +'\"%d-%m-%Y_%H:%M:%S\"'`"
DEFINES += ARTEMIS=1

# Input
HEADERS += src/runtime/runtime.h \
    src/runtime/webkitwrapper.h \
    src/webkitexecutor.h \
    src/executionresult.h \
    src/executableconfiguration.h \
    src/artemisoptions.h \
    src/inputgenerator/abstractinputgenerator.h \
    src/inputgenerator/randominputgenerator.h \
    src/inputgenerator/targets/targetdescriptor.h \
    src/inputgenerator/targets/legacytarget.h \
    src/inputgenerator/targets/jquerylistener.h \
    src/inputgenerator/targets/jquerytarget.h \
    src/input/inputsequence.h \
    src/events/forms/forminput.h \
    src/worklist/worklist.h \
    src/worklist/deterministicworklist.h \
    src/termination/terminationstrategy.h \
    src/termination/numberofiterationstermination.h \
    src/artemisapplication.h \
    src/events/domelementdescriptor.h \
    src/events/eventhandlerdescriptor.h \
    src/input/dominput.h \
    src/artemisglobals.h \
    src/events/forms/formfieldtypes.h \
    src/events/forms/formfield.h \
    src/events/eventparameters.h \
    src/events/eventypes.h \
    src/events/baseeventparameters.h \
    src/events/mouseeventparameters.h \
    src/events/keyboardeventparameters.h \
    src/executorstate.h \
    src/variants/randomvariants.h \
    src/variants/variantsgenerator.h \
    src/events/forms/formfieldvalue.h \
    src/util/randomutil.h \
    src/priortizer/abstractprioritizer.h \
    src/priortizer/randomprioritizer.h \
    src/priortizer/constantprioritizer.h \
    src/exceptionhandlingqapp.h \
    src/artemiswebpage.h \
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
    src/ajax/ajaxrequestlistener.h \
    src/ajax/ajaxrequest.h \
    src/listeners/pagerecreatelistner.h \
    src/listeners/sourceloadinglistener.h \
    src/cookies/immutablecookiejar.h \
    src/statistics/statsstorage.h \
    src/statistics/writers/pretty.h \
    src/input/baseinput.h \
    src/input/timerinput.h \
    src/browser/timer.h
SOURCES += src/runtime/runtime.cpp \
    src/runtime/webkitwrapper.cpp \
    src/webkitexecutor.cpp \
    src/executionresult.cpp \
    src/executableconfiguration.cpp \
    src/artemis.cpp \
    src/artemisoptions.cpp \
    src/inputgenerator/abstractinputgenerator.cpp \
    src/inputgenerator/randominputgenerator.cpp \
    src/inputgenerator/targets/legacytarget.cpp \
    src/inputgenerator/targets/targetdescriptor.cpp \
    src/inputgenerator/targets/jquerytarget.cpp \
    src/inputgenerator/targets/jquerylistener.cpp \
    src/input/inputsequence.cpp \
    src/events/forms/forminput.cpp \
    src/worklist/worklist.cpp \
    src/worklist/deterministicworklist.cpp \
    src/termination/terminationstrategy.cpp \
    src/termination/numberofiterationstermination.cpp \
    src/artemisapplication.cpp \
    src/events/domelementdescriptor.cpp \
    src/events/eventhandlerdescriptor.cpp \
    src/input/dominput.cpp \
    src/events/forms/formfield.cpp \
    src/events/eventparameters.cpp \
    src/events/baseeventparameters.cpp \
    src/events/eventtypes.cpp \
    src/events/mouseeventparameters.cpp \
    src/events/keyboardeventparameters.cpp \
    src/executorstate.cpp \
    src/variants/randomvariants.cpp \
    src/variants/variantsgenerator.cpp \
    src/events/forms/formfieldvalue.cpp \
    src/util/randomutil.cpp \
    src/priortizer/abstractprioritizer.cpp \
    src/priortizer/randomprioritizer.cpp \
    src/priortizer/constantprioritizer.cpp \
    src/exceptionhandlingqapp.cpp \
    src/artemiswebpage.cpp \
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
    src/ajax/ajaxrequestlistener.cpp \
    src/ajax/ajaxrequest.cpp \
    src/listeners/pagerecreatelistner.cpp \
    src/listeners/sourceloadinglistener.cpp \
    src/cookies/immutablecookiejar.cpp \
    src/statistics/statsstorage.cpp \
    src/statistics/writers/pretty.cpp \
    src/input/timerinput.cpp \
    src/browser/timer.cpp
QT += network
