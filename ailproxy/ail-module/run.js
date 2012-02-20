var ailreader = require('./build/Release/ailreader');

url = ['ajax', 'search'];
kwargs = ['query'];
vwargs = ['something'];
ail_file = '/home/semadk/src/svn/ail/benchmarks/experiments/learning/example-ail-specs/simpleajax.ail';

console.warn(ailreader.generate_response_permutation(url, kwargs, vwargs, ail_file));