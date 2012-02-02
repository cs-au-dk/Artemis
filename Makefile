help:
	@echo "Targets:"
	@echo "    webkit[-debug][-minimal] - build [a minimal] WebKit Qt port [with debug info]"
	@echo "    webkit-clean             - clean WebKit files"
	@echo ""
	@echo "    artemis                  - Build Artemis"
	@echo "    artemis-clean            - Clean artemis"
	@echo ""
	@echo "    qt-checkout              - Checkout a copy of the Qt 4.8 Framework source"
	@echo ""
	@echo "    qhash-patch              - Apply qt sourcefile patch"

webkit:
	@echo "Building release QtWebKit"
	./WebKit/Tools/Scripts/build-webkit --qt --qmakearg="DEFINES+=ARTEMIS=1" --makearg="-j4"

webkit-minimal:
	@echo "Building release QtWebKit"
	./WebKit/Tools/Scripts/build-webkit --qt --qmakearg="DEFINES+=ARTEMIS=1" --makearg="-j4"

webkit-debug:
	@echo "Building debug QtWebKit"
	./WebKit/Tools/Scripts/build-webkit --qt --qmakearg="DEFINES+=ARTEMIS=1" --makearg="-j4" --debug

webkit-debug-minimal:
	@echo "Building debug QtWebKit"
	./WebKit/Tools/Scripts/build-webkit --qt --qmakearg="DEFINES+=ARTEMIS=1" --makearg="-j4" --debug --minimal


webkit-clean:
	@echo "Cleaning WebKit BuildFiles"
	./WebKit/Tools/Scripts/build-webkit --clean

artemis:
	cd artemis-code && qmake && make

artemis-clean:
	cd artemis-code && qmake && make clean

qt-checkout:
	git clone git://gitorious.org/qt/qt.git

qhash-patch:
	patch ./qt/src/corelib/tools/qhash.h qhash.patch
