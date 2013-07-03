install-ail: install-yajl remove-yajl-folder install-node-gyp build-ail-module  

get-yajl: remove-yajl-folder
	git clone git://github.com/lloyd/yajl yajl 

install-yajl: get-yajl 
	cd yajl; ./configure && sudo make install

remove-yajl-folder: 
	rm -rf yajl

install-node-gyp:
	sudo npm -g install node-gyp

build-ail-module:  
	cd ail-module/ailreader/; make 
	cd ail-module;  sed "s?#PATH?"`pwd`"?" binding.gyp-orig > binding.gyp; node-gyp rebuild

ail-clean: 
	cd ail-module/ailreader/; make clean
	cd ail-module; node-gyp clean; rm binding.gyp

install-pp-modules:
	sudo npm -g install js-beautify
	sudo npm -g install ent 
