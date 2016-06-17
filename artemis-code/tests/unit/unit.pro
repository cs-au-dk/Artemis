
TEMPLATE = app
CONFIG += console
CONFIG -= app_bundle

CONFIG += static

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
# Override some options set in artemis-core.pri, as gmock has some warnings.
QMAKE_CXXFLAGS += -Wno-error

QMAKE_LFLAGS += '-Wl,-rpath,\'$$PWD/../../../WebKit/WebKitBuild/Release/lib\''

HEADERS += \
    include/gtest/gtest.h \
    include/gmock/gmock.h

SOURCES += \
    src/gtest/gtest_main.cc \
    src/gtest/gtest-all.cc \
    src/gmock/gmock-all.cc \
    src/strategies/inputgenerator/form/constantstringforminputgeneratortest.cpp \
    src/concolic/solver/cvc4regextest.cpp \
    src/concolic/solver/cvc4solvertest.cpp
