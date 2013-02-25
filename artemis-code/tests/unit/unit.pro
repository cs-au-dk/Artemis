
TEMPLATE = app
CONFIG += console
CONFIG -= app_bundle

LIBS += -pthread

DEFINES += ARTEMIS=1

LIBS += ../../../WebKit/WebKitBuild/Release/lib/libQtWebKit.so

INCLUDEPATH += ../../../WebKit/WebKitBuild/Release/include/ \
    ../../../WebKit/WebKitBuild/Release/include/QtWebKit/ \
    ../../../WebKit/Source/WebCore \
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
    src/runtime/worklist/deterministicworklisttest.cpp \
    src/strategies/inputgenerator/form/constantstringforminputgeneratortest.cpp
