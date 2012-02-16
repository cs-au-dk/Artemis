var http = require('http'),
    fs = require('fs'),
    url = require('url'),
    path = require('path'),
    child_process = require('child_process'),
    uuid = require('node-uuid');

var drop_dir;

var EXCLUDE_PAYLOAD = ['image/png', 'image/gif', 'image/jpg', 'image/jpeg', 'application/x-shockwave-flash']

var _uuid = uuid();
var _next_id = 0;

function getRequestResponseId() {
  return _uuid + '-' + _next_id++; 
}

function getPayloadExtension(content_type, content_encoding) {
  var extensions = {'text/html': '.html',
                    'text/css': '.css',
                    'text/xml': '.xml',
                    'text/json': '.json',
                    'application/json': '.json',
                    'text/javascript': '.js',
                    'application/javascript': '.js',
                    'application/x-javascript': '.js'};
      
  var extension = extensions[content_type];

  if (extension == undefined) {
    console.info('Unknown content-type [' + content_type + '] detected');
    extension = '';
  }

  return extension +  (content_encoding == 'gzip' ? '.gz' : '');
}

function jsonSelector(key, value) {
  var accepted = ['', 'method', 'httpVersion', 'statusCode', 'url', 'responseCode'];
    
  if (key == 'headers') return JSON.stringify(value);
  if (accepted.indexOf(key) > -1) return value;

  return undefined;
}

function decompressPayload (payload_drop_path) {
  child_process.exec('gzip -d ' + payload_drop_path,
    function(error) { if (error) {
      console.log('Error decompressing file ' + payload_drop_path);
  }});
}

function requestHandler(request, response) {
  /* Handles each incoming request to the proxy server */

  var id = getRequestResponseId();
  var base_drop_path = drop_dir + id + '.';
  
  var request_headers_path = base_drop_path + 'request-headers.json';
  var request_payload_path = base_drop_path + 'request-payload.txt';
  var response_headers_path = base_drop_path + 'response-headers.json';
  var response_payload_path = base_drop_path + 'response-payload'; 
  
  var request_headers_fp = fs.createWriteStream(request_headers_path)
  request_headers_fp.write(JSON.stringify(request, jsonSelector));
  request_headers_fp.end();
  
  var request_url = url.parse(request.url);
  
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

    var content_type = (proxy_response.headers['content-type'] || 'unknown').split(';')[0].toLowerCase();
    var content_encoding = proxy_response.headers['content-encoding'];

    /* Drop (write to file) request and response */

    var response_headers_fp = fs.createWriteStream(response_headers_path)
    response_headers_fp.write(JSON.stringify(proxy_response, jsonSelector));
    response_headers_fp.end();

    if (EXCLUDE_PAYLOAD.indexOf(content_type) == -1) {
      response_payload_path += getPayloadExtension(content_type, content_encoding);
      
      var response_payload_fp = fs.createWriteStream(response_payload_path);
  
      proxy_response.addListener('data', function(data) { 
        response_payload_fp.write(data, 'binary'); 
      });

      proxy_response.addListener('end', function() { 
        response_payload_fp.end(); 

        if (content_encoding == 'gzip') {
          decompressPayload(response_payload_path);
        } 
      
      });
    }

    /* Repeat response to the client */ 
    
    response.writeHead(proxy_response.statusCode, proxy_response.headers);

    proxy_response.addListener('data', function(chunk) {
      response.write(chunk, 'binary');
    });
    
    proxy_response.addListener('end', function() {
      response.end();
    });
  });
  
  proxy_request.on('error', function(e) {
    console.error('Error encountered when handling url ' + request.url);
    console.error(e);
  });

  var request_payload_fp = fs.createWriteStream(request_payload_path);
  
  request.addListener('data', function(chunk) {
    proxy_request.write(chunk, 'binary');
    request_payload_fp.write(chunk, 'binary');
  });
  
  request.addListener('end', function() {
    proxy_request.end();
    request_payload_fp.end();
  });

}

if (process.argv.length < 3) {
  process.stdout.write('usage: node httpdump.js /output/dir\n');
  process.exit(1);
}

drop_dir = path.join(process.argv[2], '/');
http.createServer(requestHandler).listen(8080);

process.stdout.write('proxy server created on port 8080\n');
