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
var jsbeautify = require('js-beautify');
var ent = require('ent');

var known_js_files = {};

function requestHandler(request, response) {

    var request_url = url.parse(request.url, true);
    var request_chunks = [];

    console.log("Handling: " + request_url.path);

	request.addListener('data', function(chunk) {
        request_chunks.push(chunk);
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

        var isJavaScript = request.url.indexOf('.js') != -1 ||
            request_url.path in known_js_files ||
            request.url.indexOf('ScriptResource.axd') != -1;

        var proxy_request = http.request(options, function(proxy_response) {

            var response_chunks = [];

            proxy_response.addListener('data', function(chunk) {
                response_chunks.push(chunk);
            });

            proxy_response.addListener('end', function() {

                var response_content = Buffer.concat(response_chunks);
                var response_headers = proxy_response.headers;

                var content_type_header = proxy_response.headers['content-type'];
                var accept_header = request.headers['accept'];

                var isHtml = (content_type_header != undefined && content_type_header.indexOf('html') != -1) ||
                    (accept_header != undefined && accept_header.indexOf('html') != -1);

                if (isHtml) {
                    var html = response_content.toString('utf-8');

                    var jscript_re = /<script.*src=["'](.*)["']>/ig;

                    var match;
                    while (match = jscript_re.exec(html)) {
                        if (match.length > 1) {
                            var script_url = url.parse(ent.decode(match[1]), true);
                            known_js_files[script_url.path] = true;
                        }
                    }
                }

                if (isJavaScript) {
                    response_content = new Buffer(jsbeautify.js_beautify(response_content.toString('utf-8')), 'utf-8');
                    response_headers['content-length'] = response_content.length;
                }

                response.writeHead(proxy_response.statusCode, response_headers);
                response.end(response_content);

            });

        });

        proxy_request.on('error', function() {
            console.error('Error encountered handling URL: ' + request.url);
            response.end();
        });

        proxy_request.write(Buffer.concat(request_chunks), 'binary');
        proxy_request.end();

	});
}

http.createServer(requestHandler).listen(8080);
console.log('Launched Prettify Proxy, listening on port 8080');
