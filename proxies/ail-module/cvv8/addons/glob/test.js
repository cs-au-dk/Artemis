load('../test-common.js');

assert( matchesGlob('*.*', 'README.txt') );
assert( !matchesGlob('[a-z]*', 'README.txt') );
assert( matchesGlob('[A-Z]*', 'README.txt') );
assert( !matchesLike('A%', 'README.txt') );
assert( matchesLike('R%', 'README.txt') );
assert( matchesLike('read%', 'README.txt') );
assert( !matchesLike('r%', 'README.txt', true) );
assert( !matchesGlob( null, "abc" ) );
assert( !matchesGlob( "abc", null ) );
assert( !matchesLike( null, "abc" ) );
assert( !matchesLike( "abc", null ) );
