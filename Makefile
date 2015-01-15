ARCH := $(shell uname -m)

help:
	@echo "Targets:"
	@echo "    all				- Build webkit,  artemis, and the constraint solver"
	@echo "    all-debug                    - Build webkit (debug),  artemis, and the constraint solver"
	@echo "    all-clean                    - Cleans WebKit (debug and normal) and Artemis"
	@echo ""
	@echo "    webkit-minimal[-debug] 	- Build a minimal WebKit Qt port [with debug info]"
	@echo "    webkit-clean             	- Clean WebKit files"
	@echo "    webkit-clean-debug		- Clean WebKit debug files"
	@echo ""
	@echo "    artemis                  	- Build Artemis"
	@echo "    artemis-clean            	- Clean artemis"
	@echo "    artemis-format-code		- Format artemis code"
	@echo ""
	@echo "    constraintsolver             - Build the constraint solver"
	@echo ""
	@echo "    fetch-[apt|yum]		- Fetch dependencies from [apt|yum]"
	@echo "    fetch-qt			- Fetch, configure and makes Qt"

CORES = `grep -c ^processor /proc/cpuinfo`
WEBKIT_BUILD_SCRIPT = ./WebKit/Tools/Scripts/build-webkit --qt --qmakearg="DEFINES+=ARTEMIS=1" --makearg="-j$(CORES)" --qmakearg="CC=gcc-4.7" --qmakearg="CXX=g++-4.7" --no-webkit2 --inspector --javascript-debugger
WEBKIT_TEST_SCRIPT = ./WebKit/Tools/Scripts/run-javascriptcore-tests --qmakearg="DEFINES+=ARTEMIS=1" --debug

CONTRIB_Z3 = ./contrib/Z3
CONTRIB_Z3_STR = ./contrib/Z3-str
CONTRIB_QHTTPSERVER = ./contrib/QHttpServer

build: check webkit-minimal artemis

all: webkit-minimal constraintsolver qhttpserver artemis
all-debug: webkit-minimal-debug constraintsolver qhttpserver artemis
all-clean: webkit-clean webkit-clean-debug artemis-clean 

webkit-jscore-test:
	${WEBKIT_TEST_SCRIPT}

webkit-minimal:	check check-env check-sys
	@if test -d "./WebKit/WebKitBuild/Debug"; then \
		rm -f ./WebKit/WebKitBuild/Release; \
		rm -rf ./WebKit/WebKitBuild/Debug; \
	fi
	@echo "Building minimal release QtWebKit"
	${WEBKIT_BUILD_SCRIPT} --minimal


webkit-minimal-debug: check check-env check-sys
	@echo "Building minimal debug QtWebKit"
	${WEBKIT_BUILD_SCRIPT} --debug --minimal
	@echo "Removing release version"
	@rm -rf ./WebKit/WebKitBuild/Release
	@echo "Setting up symbolic link"
	ln -s ./Debug/ ./WebKit/WebKitBuild/Release

webkit-clean: check-env
	@echo "Cleaning WebKit build"
	${WEBKIT_BUILD_SCRIPT} --clean

webkit-clean-debug:
	@echo "Cleaning WebKit build"
	${WEBKIT_BUILD_SCRIPT} --debug --clean

artemis: check-env
	cd artemis-code && qmake && make -j8

artemis-clean:
	cd artemis-code && qmake && make clean

artemis-format-code:
	cd artemis-code && astyle --style=kr --indent=spaces --break-blocks --indent-labels --pad-header --unpad-paren --break-closing-brackets --add-one-line-brackets --min-conditional-indent=0 --pad-oper --align-pointer=type --recursive "./src/*.cpp" "./src/*.h"

fetch-qt:
	git clone git://gitorious.org/qt/qt.git && cd qt && echo -e 'o\nyes\n' | ./configure -prefix `pwd` -no-webkit && make

constraintsolver:
	cd ${CONTRIB_Z3}; autoconf
	cd ${CONTRIB_Z3}; ./configure
	cd ${CONTRIB_Z3}; make
	cd ${CONTRIB_Z3}; make a

	cd ${CONTRIB_Z3_STR}; make

qhttpserver:
	cd ${CONTRIB_QHTTPSERVER}; qmake
	cd ${CONTRIB_QHTTPSERVER}; make
	cd ${CONTRIB_QHTTPSERVER}; sudo make install
	cd ${CONTRIB_QHTTPSERVER}; sudo ldconfig

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

check-env:
	@echo "Checking environment variables"
	@echo $${QTDIR:?"Please set the QTDIR environment variable to the Qt install dir"} > /dev/null;
	@echo $${ARTEMISDIR:?"Please set the ARTEMISDIR environment variable to the folder containing this Makefile"} > /dev/null;

check-sys:
	@echo "Checking system compatibility"
ifneq ($(ARCH),x86_64)
	@echo "Error: we only support 64 systems"
	@exit 1
endif

DEPENDENCIES = g++ flex bison gperf ruby cmake lemon re2c libxext-dev libfontconfig-dev libxrender-dev libsqlite3-dev php5 php5-sqlite sqlite3 qt4-qmake libqt4-core  autoconf dos2unix python-nose graphviz libqt4-dev libqt4-core libqt4-gui libqt4-opengl libqt4-opengl-dev xdot libqjson0 libqjson-dev

YUM_DEPENDENCIES = gcc-c++ flex bison gperf ruby cmake lemon re2c fontconfig-devel libXext-devel patch sqlite-devel php php-devel perl-Tk perl-Digest-MD5 autoconf dos2unix python-nose qt qt-devel glibc-static libstdc++-static python-xdot qjson qjson-devel

fetch-apt:
	sudo apt-get install ${DEPENDENCIES}
	@echo "Installing libqt4-dev-bin if available"
	-sudo apt-get install libqt4-dev-bin >/dev/null 2>/dev/null
	@echo ""
	@echo "----------------------------------"
	@echo "Fetch completed successfully"
	@echo "----------------------------------"
	@echo ""

fetch-yum:
	sudo yum install ${YUM_DEPENDENCIES}
	@echo ""
	@echo "----------------------------------"
	@echo "Fetch completed successfully"
	@echo "----------------------------------"
	@echo ""

