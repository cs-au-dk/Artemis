TEMPLATE = app
TARGET = artemis

DEPENDPATH += .
INCLUDEPATH += \
    ../WebKit/WebKitBuild/Release/include/ \
    ../WebKit/WebKitBuild/Release/include/QtWebKit/ \
    ../WebKit/Source/WebCore \
    src

CONFIG -= app_bundle

LIBS += ../WebKit/WebKitBuild/Release/lib/libQtWebKit.so

installtarget.path = $$(ARTEMIS_PATH)/bin
installtarget.files = dist/*
INSTALLS += installtarget

include(artemis-core.pri)

HEADERS += \
    src/artemisapplication.h \

SOURCES += \
    src/artemis.cpp \
    src/artemisapplication.cpp \
