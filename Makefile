UNAME := $(shell uname -s)

help:
	@echo "Targets:"
	@echo "    webkit[-minimal]       - build WebKit Qt port"
	@echo "    webkit-clean           - clean WebKit files"
	@echo "    webkit-install-into-qt - Install Qt port of Webkit into Qt installation"
	@echo ""
	@echo "    artemis                - Build Artemis"
	@echo "    artemis-clean          - Clean artemis"
	@echo ""
	@echo "    qt-checkout            - Checkout a copy of the Qt 4.8 Framework source"
	@echo ""
	@echo "    qhash-patch            - Apply qt sourcefile patch"

webkit:
	@echo "Building release QtWebKit"
	./WebKit/Tools/Scripts/build-webkit --qt --qmakearg="DEFINES+=ARTEMIS=1"

webkit-minimal:
	@echo "Build minimal webkit!"
	./WebKit/Tools/Scripts/build-webkit --qt --minimal --qmakearg="DEFINES+=ARTEMIS=1"

webkit-clean:
	@echo "Cleaning WebKit BuildFiles"
	./WebKit/Tools/Scripts/build-webkit --clean

webkit-install-into-qt:
	@if test -d ./qt/include/QtWebKit; then echo "WebKit dir present in Qt weinstall"; else mkdir ./qt/include/QtWebKit; fi
ifeq ($(UNAME),Linux)
	@cp -rv ./WebKit/WebKitBuild/Release/lib/libQtWebKit* ./qt/lib
endif
ifeq ($(UNAME),Darwin)
	@cp -rv ./WebKit/WebKitBuild/Release/lib/QtWebKit.framework ./qt/lib
endif
	@cp -v ./WebKit/WebKitBuild/Release/include/QtWebKit/Q* ./qt/include/QtWebKit
	@cp -v ./WebKit/Source/WebKit/qt/Api/*.h ./qt/include/QtWebKit
	@if test -d ./qt/include/QtWebKit/instrumentation; then echo "Instrumentation dir present in Qt install"; else mkdir ./qt/include/QtWebKit/instrumentation; fi
	@cp -v ./WebKit/Source/WebCore/instrumentation/executionlistener.h ./qt/include/QtWebKit/instrumentation

artemis:
	cd artemis-code && qmake -spec linux-llvm && LD_LIBRARY_PATH=/home/kja/Artemis/WebKit/WebKitBuild/Release/lib dragonegg_disable_version_check=1 make

artemis-clean:
	cd artemis-code && qmake -spec linux-llvm && make clean

qt-checkout:
	git clone git://gitorious.org/qt/qt.git; cd qt; git checkout v4.8.0

qhash-patch:
	patch ./qt/src/corelib/tools/qhash.h qhash.patch