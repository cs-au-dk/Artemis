help:
	@echo "Targets:"
	@echo "    install			- install webkit and artemis"
	@echo "    webkit-minimal[-debug] 	- build a minimal WebKit Qt port [with debug info]"
	@echo "    webkit-clean             	- clean WebKit files"
	@echo ""
	@echo "    artemis                  	- Build Artemis"
	@echo "    artemis-clean            	- Clean artemis"
	@echo "    artemis-install		- install artemis"
	@echo "    artemis-format-code		- formats artemis code"
	@echo ""
	@echo "    fetch-[apt|yum]		- fetching dependencies from [apt|yum]"
	@echo "    fetch-qt			- fetches, configures and makes Qt"

WEBKIT_BUILD_SCRIPT = ./WebKit/Tools/Scripts/build-webkit --qt --qmakearg="DEFINES+=ARTEMIS=1" --makearg="-j4"  --qmakearg="CC=gcc-4.7" --qmakearg="CXX=g++-4.7" --inspector --javascript-debugger

build: check webkit artemis

install: webkit-install artemis-install

webkit-install: webkit-minimal

webkit-minimal:	check check-env
	@echo "Building minimal release QtWebKit"
	${WEBKIT_BUILD_SCRIPT} --minimal


webkit-minimal-debug: check check-env
	@echo "Building minimal debug QtWebKit"
	${WEBKIT_BUILD_SCRIPT} --debug --minimal

webkit-clean:
	@echo "Cleaning WebKit build"
	${WEBKIT_BUILD_SCRIPT} --clean

artemis:
	cd artemis-code && qmake && make -j4

artemis-clean:
	cd artemis-code && qmake && make clean

artemis-install: artemis
	cd artemis-code && make install

artemis-format-code:
	cd artemis-code && astyle --style=kr --indent=spaces --break-blocks --indent-labels --pad-header --unpad-paren --break-closing-brackets --add-one-line-brackets --min-conditional-indent=0 --pad-oper --align-pointer=type --recursive "./src/*.cpp" "./src/*.h"

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
check-env:
	@echo "Checking environment variables"
	@echo $${QTDIR:?"Please set the QTDIR environment variable to the Qt install dir"} > /dev/null;

DEPENDENCIES = g++ flex bison gperf ruby cmake lemon re2c libxext-dev libfontconfig-dev libxrender-dev libsqlite3-dev php5

YUM_DEPENDENCIES = gcc-c++ flex bison gperf ruby cmake lemon re2c fontconfig-devel libXext-devel patch sqlite-devel php

fetch-apt:
	sudo apt-get install ${DEPENDENCIES}

fetch-yum:
	sudo yum install ${YUM_DEPENDENCIES}
