TEMPLATE = app
TARGET = artemis

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

CONFIG -= app_bundle


installtarget.path = $$(ARTMIS_PATH)/bin
installtarget.files = dist/*
INSTALLS += installtarget

include(artemis-core.pri)

HEADERS += \
    src/artemisapplication.h \

SOURCES += \
    src/artemis.cpp \
    src/artemisapplication.cpp \
