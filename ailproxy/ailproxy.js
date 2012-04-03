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

var AILReader;

var MAX_RANDOM_INT = 200;
var MAX_RANDOM_ARRAY = 20;
var MAX_RANDOM_STRING = 8;
var MAX_RANDOM_PROPERTIES = 8;

function randInt(max_value) {
	value = Math.floor(Math.random() * (max_value+1));

	if (value > max_value) {
		// Math.random can return 1
		// avoid returning max_value+1 in that case
		return max_value; 
	}

	return value;
}

function randomJson() {

	var generators;

	function getGenerator(max) {
		range = generators.length - 1;

		if (max != undefined) {
			range = max;
		}

		return generators[randInt(range)];
	}

	var rand_chars = "abcdefghijklmnopqrstuvwxyz";

	function _randomString() {
	    var text = new Array();
	    
	    for (i = 0; i < MAX_RANDOM_STRING; i++) {
	        text.push(rand_chars.charAt(randInt(rand_chars.length - 1)));
	    }

	    return text.join('');
	}

	generators = [
		function() {
			// array
			array = new Array();

			num_elements = randInt(MAX_RANDOM_ARRAY);

			if (num_elements == 0) {
				return '[]';
			}

			generator = getGenerator();

			for (i = 0; i < num_elements; i++) {
				array.push(',')
				array.push(generator());
			}

			array[0] = "["; // replace first "," with a [
			array.push("]");

			return array.join('');
		},
		function() {
			// object
			obj = new Array();

			num_properties = randInt(MAX_RANDOM_PROPERTIES);

			if (num_properties == 0) {
				return '{}';
			}

			for (i = 0; i < num_properties; i++) {
				obj.push(',');
				obj.push('"' + _randomString() + '":');
				obj.push(getGenerator()());
			}

			obj[0] = '{'; // replace first , with a {
			obj.push('}');

			return obj.join('');
		},
		function() {
			// boolean
			values = ["True", "False"];
			return values[randInt(1)];
		},
		function() {
			// integer
			return '' + Math.floor(Math.random() * MAX_RANDOM_INT);
		},
		function() {
			// string
			return '<string>';
		},
		function() {
			// null
			return 'null';
		},
		function() {
			// float
			return '' + Math.random();
		}
	];

	return getGenerator(1)();
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
	    values[i] = assoArray[key];
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

	try {
		server_cache[filename] = fs.readFileSync(full_path);
	} catch(err) {
		server_cache[filename] = null;
	}
}


function requestHandler(request, response) {
   
    var request_url = url.parse(request.url, true);
    var opArgs = trimEmpty(request_url.pathname.split('/'));
    var queryKeys = extractKeyset(request_url.query);
    var queryValues = extractValues(request_url.query);
    var request_data = "";

	request.addListener('data', function(chunk) {
	    request_data = request_data + chunk;
	});

	request.addListener('end', function() {

		var lines = request_data.split("&");
		for (i = 0; i < lines.length; i++) {
			keyvalue = lines[i].split("=");

			if (keyvalue.length == 2) {
				queryKeys.push(keyvalue[0]);
				queryValues.push(keyvalue[1]);
			}
		}

		var ailResponse = AILReader.generateResponse(opArgs, queryKeys, queryValues);

		if (ailResponse != undefined) {
			
			if (random_mode == false) {
				
				console.log('AIL ', request.url);

				response.writeHead(200, {
			    'Content-Length' : ailResponse.length,
			    'Content-Type'   : 'application/json'});
			
				response.write(ailResponse);
				response.end();

			} else {

				console.log('AIL-RANDOM ', request.url);

				response.writeHead(200, {
			    'Content-Type'   : 'application/json'});
				
				random_json = randomJson();

				response.write(random_json);
				response.end();				
			}
		
		} else if (server_only_mode) {

			filename = (request_url.pathname || 'index.html');

			if (server_cache[filename] == undefined) {
				serverPrefetch(filename);
			}

			if (server_cache[filename]) {

				console.log('SERVER-CACHED ', request.url, " (", filename, ")");

				response.writeHead(200, {
		    		'Content-Type'   : 'text/html'});

				response.write(server_cache[filename], 'binary');
				response.end();

			} else {

				console.log('SERVER-EMPTY ', request.url, " (", filename, ")");

				response.writeHead(200, {
		    		'Content-Type'   : 'text/html'});
				response.end();		
			}

		} else {

			console.log('PROXY ', request.url);
		
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
    console.log('Error, proper usage: node ailproxy.js /path/to/schema [--server-only-mode /path/to/files | --random-mode]');
} else {
	server_only_mode = (process.argv.length > 3 && process.argv[3] == '--server-only-mode');
	random_mode = (process.argv.length > 3 && process.argv[3] == '--random-mode');

	if (process.argv.length > 4) {
		server_base_dir = process.argv[4];
	}

    AILReader = new ail.Reader(process.argv[2]);
    http.createServer(requestHandler).listen(8080);
    console.log('Launched AIL Proxy, listening on port 8080');
}