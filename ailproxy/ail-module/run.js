var ail = require('./build/Release/AIL');

var url = ['ajax', 'search'];
var kwargs = ['query'];
var vwargs = ['something'];
var schema_path = './tests/schema.ail';

var reader = new ail.Reader(schema_path);
console.log(reader.generateResponse(url, kwargs, vwargs));
console.log(reader.generateResponse(url, kwargs, vwargs));