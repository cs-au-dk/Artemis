TEMPLATE = app
TARGET = artemis

CONFIG += static

DEPENDPATH += .
debugart {
INCLUDEPATH += \
    ../WebKit/WebKitBuild/Debug/include/ \
    ../WebKit/WebKitBuild/Debug/include/QtWebKit/ \
    ../WebKit/Source/JavaScriptCore/runtime/ \
    ../WebKit/Source/JavaScriptCore/ \
    ../WebKit/Source/WebCore/ \
    ../WebKit/Source/WTF/ \
    ../WebKit/Source/ \
    src
LIBS += ../WebKit/WebKitBuild/Debug/lib/libQtWebKit.so
} else {
INCLUDEPATH += \
    ../WebKit/WebKitBuild/Release/include/ \
    ../WebKit/WebKitBuild/Release/include/QtWebKit/ \
    ../WebKit/Source/JavaScriptCore/runtime/ \
    ../WebKit/Source/JavaScriptCore/ \
    ../WebKit/Source/WebCore/ \
    ../WebKit/Source/WTF/ \
    ../WebKit/Source/ \
    src
LIBS += ../WebKit/WebKitBuild/Release/lib/libQtWebKit.so
}

installtarget.path = $$(ARTMIS_PATH)/bin
installtarget.files = dist/*
INSTALLS += installtarget

include(artemis-core.pri)

debugart {
    QMAKE_LFLAGS += '-Wl,-rpath,\'$$PWD/../WebKit/WebKitBuild/Release/lib\''
} else {
    QMAKE_LFLAGS += '-Wl,-rpath,\'$$PWD/../WebKit/WebKitBuild/Debug/lib\''
}

HEADERS += \
    src/artemisapplication.h

SOURCES += \
    src/artemis.cpp \
    src/artemisapplication.cpp
