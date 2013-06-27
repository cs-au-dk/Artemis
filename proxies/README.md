Installing and running proxies
==============================

AIL Proxy
---------

[desc]

###Install###

1. Install node.js and npm from http://nodejs.org. 

   For installation by package manager see https://github.com/joyent/node/wiki/Installing-Node.js-via-package-manager .

2. Install AIL
   
       make install-ail

   This will install the latest version of yajl, node-gyp and eventually build the AIL module.

### Run ###

1. Run AIL proxy
    
       node ailproxy.js <path to schema> <options>

   Run ````node ailproxy.js```` for more information 

Prettify Proxy
--------------

Prettify Proxy is a web proxy for automatically prettifying JavaScript code. All requests to files containing ".js" will be passed through JSBeautifier (http://jsbeautifier.org), while all other requests are passed through untouched.

A number of herustics is used to identify JavaScript files. Including HTML file inspection and matching on file known filenaming conventions.

The proxy requires node.js (http://nodejs.org/) and the js-beautify package (https://npmjs.org/package/js-beautify).

NOTE: The Prettify Proxy does not handle SSL connections well. The suggested solution, if a website uses SSL, is to download the website and create a non-SSL version of it.

###Install###


1. Install node.js and npm from http://nodejs.org. For installation by package manager see https://github.com/joyent/node/wiki/Installing-Node.js-via-package-manager .

2. Install modules
   
       make install-pp-modules 

###Run###

3. Set node.js module path (e.g. for Ubuntu)

       export NODE_PATH=/usr/local/lib/node_modules/

3. Run

       node prettifyproxy.js

4. Run with Artemis
	
   Add the argument -t localhost:8080 to Artemis to direct all traffic through the proxy.

   Notice, that Artemis ignores the -t argument if it operates on content hosted on the localhost domain[1].


[1] https://github.com/cs-au-dk/Artemis/issues/46