var http = require('http');
var url = require('url');
var path = require('path');
var ail = require('./ail-module/build/Release/AIL');

var AILReader;

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
			
			console.log('AIL ', request.url);

			response.writeHead(200, {
		    'Content-Length' : ailResponse.length,
		    'Content-Type'   : 'application/json'});
		
			response.write(ailResponse);
			response.end();
		
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

if (process.argv.length != 3) {
    console.log('Error, proper usage: node ailproxy.js /path/to/schema');
} else {
    AILReader = new ail.Reader(process.argv[2]);
    http.createServer(requestHandler).listen(8080);
    console.log('Launched AIL Proxy, listening on port 8080');
}