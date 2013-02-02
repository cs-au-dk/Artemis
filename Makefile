help:
	@echo "Targets:"
	@echo "    webkit[-debug][-minimal] - build [a minimal] WebKit Qt port [with debug info]"
	@echo "    webkit-clean             - clean WebKit files"
	@echo ""
	@echo "    artemis                  - Build Artemis"
	@echo "    artemis-clean            - Clean artemis"
	@echo ""
	@echo "    qt-checkout              - Checkout a copy of the Qt 4.8 Framework source"

WEBKIT_BUILD_SCRIPT = ./WebKit/Tools/Scripts/build-webkit --qt --qmakearg="DEFINES+=ARTEMIS=1" --makearg="-j4"  --qmakearg="CC=gcc-4.7" --qmakearg="CXX=g++-4.7"

build: check webkit artemis

install: webkit-install artemis-install

webkit: check
	@echo "Building release QtWebKit"
	${WEBKIT_BUILD_SCRIPT}

webkit-install: webkit
	mkdir -p ${ARTEMIS_PATH}/WebKit/WebKitBuild
	cp -r ./WebKit/WebKitBuild/* ${ARTEMIS_PATH}/WebKit/WebKitBuild

webkit-minimal:
	@echo "Building minimal release QtWebKit"
	${WEBKIT_BUILD_SCRIPT} --minimal

webkit-debug:
	@echo "Building debug QtWebKit"
	${WEBKIT_BUILD_SCRIPT} --debug

webkit-debug-minimal:
	@echo "Building minimal debug QtWebKit"
	${WEBKIT_BUILD_SCRIPT} --debug --minimal

webkit-clean:
	@echo "Cleaning WebKit build"
	${WEBKIT_BUILD_SCRIPT} --clean

artemis:
	cd artemis-code && qmake && make

artemis-clean:
	cd artemis-code && qmake && make clean

artemis-install: artemis
	cd artemis-code && make install

fetch-qt:
	git clone git://gitorious.org/qt/qt.git && cd qt && echo -e 'o\nyes\n' | ./configure -prefix `pwd` -no-webkit && make

check:
	@echo "Testing for software dependencies - if an error occurs, consult your local package manager for the program immeadiately checked for"
	which g++ > /dev/null
	which qmake > /dev/null
	which flex > /dev/null
	which bison > /dev/null
	which gperf > /dev/null
	which ruby > /dev/null
	which cmake > /dev/null
	which lemon > /dev/null
	which re2c > /dev/null

DEPENDENCIES = g++ flex bison gperf ruby cmake lemon re2c libxext-dev libfontconfig-dev libxrender-dev libsqlite3-dev

YUM_DEPENDENCIES = gcc-c++ flex bison gperf ruby cmake lemon re2c fontconfig-devel libXext-devel patch libsqlite3-dev

fetch-apt:
	sudo apt-get install ${DEPENDENCIES}

fetch-yum:
	sudo yum install ${YUM_DEPENDENCIES}
