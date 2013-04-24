/*
 * Copyright 2013 Aarhus University
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
var jsbeautify = require('js-beautify')

function requestHandler(request, response) {
    var request_url = url.parse(request.url, true);
    var request_data = "";

	request.addListener('data', function(chunk) {
	    request_data = request_data + chunk;
	});

	request.addListener('end', function() {

		var target = request.headers['host'].split(':');
		var hostname = target[0];
		var port = (target.length > 1) ? target[1] : 80;

        request.headers['accept-encoding'] = ""; // disable gzip and inflate encodings

        var options = {
            host: hostname,
            port: port,
            method: request.method,
            path: (request_url.pathname || '/') + (request_url.search || ''),
            headers: request.headers
        };

        var isJavaScript = request.url.indexOf('.js') != -1;

        var proxy_request = http.request(options, function(proxy_response) {

            response.writeHead(proxy_response.statusCode, proxy_response.headers);

            if (isJavaScript) {

                var response_data = "";

                proxy_response.addListener('data', function(chunk) {
                    response_data = response_data + chunk.toString("utf-8");
                });

                proxy_response.addListener('end', function() {
                    response.write(jsbeautify.js_beautify(response_data), 'utf-8');
                    response.end();
                });

            } else {

                proxy_response.addListener('data', function(chunk) {
                    response.write(chunk, 'binary');
                });

                proxy_response.addListener('end', function() {
                    response.end();
                });

            }

        });

        proxy_request.on('error', function() {
            console.error('Error encountered handling URL: ' + request.url);
            response.end();
        });

        proxy_request.write(request_data, 'binary');
        proxy_request.end();

	});
}

http.createServer(requestHandler).listen(8080);
console.log('Launched Prettify Proxy, listening on port 8080');
