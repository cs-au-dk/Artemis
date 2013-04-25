load('../test-common.js');
function test1() {
    asserteq( '03', sprintf('%02d', 3) );
    asserteq( 'hi, world', sprintf('%s, %s','hi','world') );
    asserteq( '42.24', sprintf('%2.2f', 42.243) );
    assertThrows( function() {
       sprintf("%s%d",'not enough arguments');
    });
}

test1();
