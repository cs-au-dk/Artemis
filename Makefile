help:
	@echo "Targets:"
	@echo "    webkit-pull         - merge changes in the WebKit source into working copy"
	@echo "    webkit-checkout     - checkout the source WebKit trunk. Requires a working gitorious.org account"
	@echo "    webkit-build        - build WebKit Qt port"
	@echo "    webkit-clean        - clean WebKit files"
	@echo "    webkit-build-debug  - build WebKit Qt port with debugging"
	@echo "    webkit-build-minimal- build WebKit with a minimum of functionality" 
	@echo ""
	@echo "    set-qt-path         - Set path to include qmake"
	@echo ""
	@echo "    artemis             - Build Artemis"
	@echo "    artemis-clean       - Clean artemis"
	@echo "    artemis-checkout    - Checkout Simonhj edition of Artemis Source"
	@

webkit-pull:
	@echo "Pulling and merging changes to the WebKit trunk"
	cd WebKit; git pull

webkit-checkout:
	@echo "Checking out the WebKit trunk"
	git clone git@gitorious.org/webkit/webkit.git WebKit

webkit:
	@echo "Building release QtWebKit"
	./WebKit/Tools/Scripts/build-webkit --qt --qmakearg="DEFINES+=ARTEMIS=1"

webkit-build-debug:
	@echo "Building WebKit"
	./WebKit/Tools/Scripts/build-webkit --qt --debug --qmakearg="DEFINES+=ARTEMIS=1"

webkit-build-minimal:
	@echo "Build minimal webkit!"
	./WebKit/Tools/Scripts/build-webkit --qt --minimal --qmakearg="DEFINES+=ARTEMIS=1"

webkit-build-minimal-debug:
	@echo "Build minimal webkit!"
	./WebKit/Tools/Scripts/build-webkit --qt --debug --minimal --qmakearg="DEFINES+=ARTEMIS=1"

webkit-clean:
	@echo "Cleaning WebKit BuildFiles"
	./WebKit/Tools/Scripts/build-webkit --clean

webkit-install-into-qt:
	@if test -d ./qt/include/QtWebKit; then echo "WebKit dir present in Qt install"; else mkdir ./qt/include/QtWebKit; fi
	@cp -rv ./WebKit/WebKitBuild/Release/lib/libQtWebKit* ./qt/lib
	@cp -v ./WebKit/WebKitBuild/Release/include/QtWebKit/* ./qt/include/QtWebKit
	@cp -v ./WebKit/Source/WebKit/qt/Api/*.h ./qt/include/QtWebKit
	@if test -d ./qt/include/QtWebKit/instrumentation; then echo "instrumentation dir present in Qt install"; else mkdir ./qt/include/QtWebKit/instrumentation; fi
	@cp -v ./WebKit/Source/WebCore/instrumentation/executionlistener.h ./qt/include/QtWebKit/instrumentation



setup-qt-env:
	source setup-qt-env

artemis-checkout:
	hg clone https://bitbucket.org/simonhj/artemis2

artemis:
	cd artemis-code && qmake && make

artemis-clean:
	cd artemis-code && qmake && make clean

qt-checkout:
	git clone git://gitorious.org/qt/qt.git; cd qt; checkout 4.8

state-index-files:
	od -txC -v artemis-code/etc/index-footer.html | sed -e "s/^[0-9]*//" | tr -s " " | sed -E -e "s/([0-9a-f]+)/0x\1,/g" > artemis-code/src/index-footer.dat 
	od -txC -v artemis-code/etc/index-header.html | sed -e "s/^[0-9]*//" | tr -s " " | sed -E -e "s/([0-9a-f]+)/0x\1,/g" > artemis-code/src/index-header.dat
