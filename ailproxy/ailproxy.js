/*
 * Copyright 2012 Aarhus University
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

var http = require('http');
var url = require('url');
var path = require('path');
var ail = require('./ail-module/build/Release/AIL');
var fs = require('fs');
var path = require('path');

var server_only_mode = false;
var random_mode = false;
var server_base_dir = null;
var server_cache = {};
var server_cached_file = {};

var AILReader;

var MAX_RANDOM_INT = 200;
var MAX_RANDOM_ARRAY = 20;
var MAX_RANDOM_STRING = 8;
var MAX_RANDOM_PROPERTIES = 8;

var ETAG_PREFIX = "" + Math.floor(Math.random()*10000);

function randInt(max_value) {
	value = Math.floor(Math.random() * (max_value+1));

	if (value > max_value) {
		// Math.random can return 1
		// avoid returning max_value+1 in that case
		return max_value; 
	}

	return value;
}

var rand_chars = "abcdefghijklmnopqrstuvwxyz";

function _randomString() {
    var text = new Array();
    
    for (i = 0; i < MAX_RANDOM_STRING; i++) {
        text.push(rand_chars.charAt(randInt(rand_chars.length - 1)));
    }

    return text.join('');
}

function randomJson(type) {

	NUM_TYPES = 7;

	if (type == undefined) {
		type = randInt(1);
	}

	if (type == 0) {
	// Object generator

		var obj = new Array();
		var num_properties = randInt(MAX_RANDOM_PROPERTIES);

		if (num_properties == 0) {
			return '{}';
		}

		obj.push('{');

		for (i = 0; i < num_properties; i++) {
			if (i != 0) {
				obj.push(',');
			}
			
			obj.push('"' + _randomString() + '":');
			obj.push(randomJson(randInt(NUM_TYPES-1)));
		}

		obj.push('}');

		return obj.join('');
	
	} else if (type == 1) {
		// Array generator
	
		var array = new Array();
		var num_elements = randInt(MAX_RANDOM_ARRAY);

		if (num_elements == 0) {
			return '[]';
		}

		var t = randInt(NUM_TYPES-1);

		array.push("[");

		for (i = 0; i < num_elements; i++) {
			if (i != 0) {
				array.push(',')
			}
			
			array.push(randomJson(t));
		}

		array.push("]");

		return array.join('');
	
	} else if (type == 2) {
		// boolean generator

		values = ["true", "false"];
		return values[randInt(1)];
	
	} else if (type == 3) {
		// integer generator
		return '' + Math.floor(Math.random() * MAX_RANDOM_INT);
	
	} else if (type == 4) {
		// string generator
		return '"<string>"';
	
	} else if (type == 5) {
		// null generator
		return 'null';
	
	} else if (type == 6) {
		// float generator
		return '' + Math.random(); 
	
	} else {
		throw "ERROR, should not reach this state";
	}

}

function extractKeyset(assoArray) {
    if (assoArray.length == 0) {
	return {};
    } else {
	var keyset = new Array();
	var i = 0;
	for (key in assoArray) {
	    keyset[i] = key;
	    i = i + 1;
	}
	return keyset;
    }
}

function extractValues(assoArray) {
    if (assoArray.length == 0) {
	return {};
    } else {
	var values = new Array();
	var i = 0;
	for (key in assoArray) {
		if (assoArray[key] == "") {
			values[i] = "-";
		} else {
			values[i] = assoArray[key];
		}
	    i = i + 1;
	}
	return values;
    }
}

function trimEmpty(list) {
	var new_list = []

	for (i = 0; i < list.length; i++) {
		if (list[i] != '') {
			new_list.push(list[i]);
		}
	}

	return new_list;
}

function serverPrefetch(filename) {
	var full_path = path.join(server_base_dir, filename);
	server_cached_file[filename] = true;

	try {
		server_cache[filename] = fs.readFileSync(full_path);
	} catch(err) {
		server_cache[filename] = false;
	}
}

function serverCachedResponse(filename, response) {
	//console.log("Fasth path");
	if (server_cache[filename]) {

		//console.log('SERVER-CACHED ', request.url, " (", filename, ")");

		response.writeHead(200, {
			'Cache-Control'	 : 'max-age=0, must-revalidate',
			'Last-Modified'  : 'Thu, 22 Mar 2012 09:09:26 GMT',
			'ETag'			 : "\"" + ETAG_PREFIX + filename + "\"",
    		'Content-Type'   : 'text/html'});

		response.write(server_cache[filename], 'binary');
		response.end();

	} else {

		//console.log('SERVER-EMPTY ', request.url, " (", filename, ")");

		response.writeHead(200, {
			'Cache-Control'	 : 'max-age=0, must-revalidate',
			'Last-Modified'  : 'Thu, 22 Mar 2012 09:09:26 GMT',
			'ETag'			 : "\"" + ETAG_PREFIX + filename + "\"",
    		'Content-Type'   : 'text/html'});
		response.end();		
	}
}


function requestHandler(request, response) {
    var request_url = url.parse(request.url, true);
    var request_data = "";

	request.addListener('data', function(chunk) {
	    request_data = request_data + chunk;
	});

	request.addListener('end', function() {

		var filename = (request_url.pathname || 'index.html');
		filename = filename.replace(/\//g, '');

		if (server_cached_file[filename]) {

			if (request.headers['if-modified-since'] != undefined ||
				request.headers['if-none-match'] != undefined) {
				// fastpath, let the client use the cached version
				
				//console.log('SERVER-304-CACHE ', request.url);

				response.writeHead(304);
				response.end();
				return;
			}

			serverCachedResponse(filename, response);
			return;
		}

		var opArgs = trimEmpty(request_url.pathname.split('/'));
    	var queryKeys = extractKeyset(request_url.query);
    	var queryValues = extractValues(request_url.query);

		var lines = request_data.split("&");

		for (i = 0; i < lines.length; i++) {
			keyvalue = lines[i].split("=");

			if (keyvalue.length == 2) {
				queryKeys.push(keyvalue[0]);
				queryValues.push(keyvalue[1]);
			} else if (keyvalue[0].length > 0) {
				queryKeys.push(keyvalue[0]);
				queryValues.push("");
			}
		}

		var ailResponse = AILReader.generateResponse(opArgs, queryKeys, queryValues);

		if (ailResponse != undefined) {
			
			if (random_mode == false) {
				
				//console.log('AIL ', request.url);

				response.writeHead(200, {
			    'Content-Length' : ailResponse.length,
			    'Content-Type'   : 'application/json'});

				response.write(ailResponse);
				response.end();

			} else {

				//console.log('AIL-RANDOM ', request.url);

				response.writeHead(200, {
			    'Content-Type'   : 'application/json'});
				
				random_json = randomJson();
				response.write(random_json);
				response.end();				
			}
		
		} else if (server_only_mode) {

			if (server_cached_file[filename] == undefined) {
				serverPrefetch(filename);
			}

			serverCachedResponse(filename, response);
			return;

		} else {

			//console.log('PROXY ', request.url);
		
			target = request.headers['host'].split(':');
			hostname = target[0];
			port = (target.length > 1) ? target[1] : 80;

			var options = {
			    host: hostname,
			    port: port,
			    method: request.method, 
			    path: (request_url.pathname || '/') + (request_url.search || ''), 
			    headers: request.headers
			}

			var proxy_request = http.request(options, function(proxy_response) {

			    response.writeHead(proxy_response.statusCode, proxy_response.headers);
			    
			    proxy_response.addListener('data', function(chunk) {
					response.write(chunk, 'binary');
			    });

			    proxy_response.addListener('end', function() {
					response.end();
			    });
			    
			});

			proxy_request.on('error', function(e) {
			    console.error('Error encountered handling URL: ' + request.url);
			    response.end();
			});

			proxy_request.write(request_data, 'binary');
			proxy_request.end();

		}
	});
}

if (process.argv.length < 3) {
    console.log('Error, proper usage: node ailproxy.js /path/to/schema [--server-only-mode /path/to/files] [--random-mode]');
} else {
	server_only_mode = (process.argv.length > 3 && process.argv[3] == '--server-only-mode');
	random_mode = (process.argv.length > 3 && process.argv[3] == '--random-mode');
	random_mode = random_mode || (process.argv.length > 5 && process.argv[5] == '--random-mode');

	if (process.argv.length > 4) {
		server_base_dir = process.argv[4];
	}

    AILReader = new ail.Reader(process.argv[2]);
    http.createServer(requestHandler).listen(8080);
    console.log('Launched AIL Proxy, listening on port 8080');
}
