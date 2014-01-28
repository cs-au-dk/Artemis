
TEMPLATE = app
CONFIG += console
CONFIG -= app_bundle

LIBS += -pthread

DEFINES += ARTEMIS=1

LIBS += ../../../WebKit/WebKitBuild/Release/lib/libQtWebKit.so

INCLUDEPATH += ../../../WebKit/WebKitBuild/Release/include/ \
    ../../../WebKit/WebKitBuild/Release/include/QtWebKit/ \
    ../../../WebKit/Source/JavaScriptCore/runtime/ \
    ../../../WebKit/Source/JavaScriptCore/ \
    ../../../WebKit/Source/WebCore/ \
    ../../../WebKit/Source/WTF/ \
    ../../../WebKit/Source/ \
    ../../src/

VPATH += ../../
include(../../artemis-core.pri)

HEADERS += \
    include/gtest/gtest.h \
    include/gmock/gmock.h

SOURCES += \
    src/gtest/gtest_main.cc \
    src/gtest/gtest-all.cc \
    src/gmock/gmock-all.cc \
    src/strategies/inputgenerator/form/constantstringforminputgeneratortest.cpp \
    src/concolic/solver/cvc4regextest.cpp
