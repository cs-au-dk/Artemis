install-ail: install-yajl remove-yajl-folder install-node-gyp build-ail-module  

get-yajl: remove-yajl-folder
	git clone git://github.com/lloyd/yajl yajl 

install-yajl: get-yajl 
	cd yajl; ./configure && sudo make install

remove-yajl-folder: 
	rm -rf yajl

install-node-gyp:
	sudo npm -g install node-gyp

build-ail-module: install-node-gyp 
	cd ail-module; 	node-gyp configure; node-gyp build

ail-clean: 
	cd ail-module; node-gyp clean

install-pp-modules:
	sudo npm -g install js-beautify
	sudo npm -g install ent 
