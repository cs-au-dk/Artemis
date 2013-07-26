ARCH := $(shell uname -m)

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

CORES = `grep -c ^processor /proc/cpuinfo`
WEBKIT_BUILD_SCRIPT = ./WebKit/Tools/Scripts/build-webkit --qt --qmakearg="DEFINES+=ARTEMIS=1" --makearg="-j$(CORES)" --qmakearg="CC=gcc-4.7" --qmakearg="CXX=g++-4.7" --no-webkit2 --inspector --javascript-debugger
WEBKIT_TEST_SCRIPT = ./WebKit/Tools/Scripts/run-javascriptcore-tests --qmakearg="DEFINES+=ARTEMIS=1" --debug

build: check webkit-minimal artemis

install: webkit-install artemis-install

webkit-install: webkit-minimal

webkit-jscore-test:
	${WEBKIT_TEST_SCRIPT}

webkit-minimal:	check check-env check-sys
	@echo "Building minimal release QtWebKit"
	${WEBKIT_BUILD_SCRIPT} --minimal


webkit-minimal-debug: check check-env check-sys
	@echo "Building minimal debug QtWebKit"
	${WEBKIT_BUILD_SCRIPT} --debug --minimal

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
	@echo $${ARTEMISDIR:?"Please set the ARTEMISDIR environment variable to the folder containing this Makefile"} > /dev/null;

check-sys:
	@echo "Checking system compatibility"
ifneq ($(ARCH),x86_64)
	@echo "Error: we only support 64 systems"
	@exit 1
endif

DEPENDENCIES = g++ flex bison gperf ruby cmake lemon re2c libxext-dev libfontconfig-dev libxrender-dev libsqlite3-dev php5 libqt4-dev-bin qt4-qmake libqt4-core  

YUM_DEPENDENCIES = gcc-c++ flex bison gperf ruby cmake lemon re2c fontconfig-devel libXext-devel patch sqlite-devel php perl-Tk perl-Digest-MD5

fetch-apt:
	sudo apt-get install ${DEPENDENCIES}

fetch-yum:
	sudo yum install ${YUM_DEPENDENCIES}
	
test-solver: check-env
	@echo "Testing solver"
	@${ARTEMISDIR}/contrib/Kaluza/artemiskaluza.sh ${ARTEMISDIR}/contrib/Kaluza/test.txt
	@cat /tmp/kaluza-result | grep "tmp1 true"
	@rm /tmp/kaluza-result
	@echo "..success.."
