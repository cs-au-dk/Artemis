load('../test-common.js');
//ByteArray.enableDestructorDebug(true);
function test1()
{
    var ba = new ByteArray(10);
    print('ba='+ba);
    ba[0] = 72; ba[1]=105;
    assertThrows( function() { ba[0] = 256; } );
    print('as string: '+ba.stringValue());
    ba.destroy();
    ba = new ByteArray("hi, world");
    print("new ba="+ba+': '+ba.stringValue());
    var i, b2;
    for( i = 0; i < 3; ++i ) {
        b2 = new ByteArray("!");
        ba.append(b2);
        b2.destroy();
    }
    print("Appended ba ("+ba.length+" bytes): "+ba.stringValue());
    for( i = 0; i < 3; ++i ) {
        ba.append("?");
    }
    print("Appended ba ("+ba.length+" bytes): "+ba.stringValue());
    for( i = 0; i < 3; ++i ) {
        ba.append(42 /* '*' */);
    }
    print("Appended ba ("+ba.length+" bytes): "+ba.stringValue());
    b2 = new ByteArray(ba);
    asserteq( ba.length, b2.length );
    ba.destroy();
    b2.destroy();
    
    var str = 'Äaöoüu';
    ba = new ByteArray(str);
    asserteq( 9, ba.length );
    asserteq( str, ba.stringValue() );
    ba.destroy();
}

function testGZip()
{
    print("Starting gzip tests...");
    var ba = new ByteArray();
    assert( !ba.isGzipped, '!ba.isGzipped' );
    var i;
    for( i = 0; i < 10; ++i ) ba.append("Line #"+i+"\n");
    var origString = ba.stringValue();
    var z = ba.gzip(z);
    assert( z instanceof ByteArray );
    assert( z.isGzipped, 'z.isGzipped' );
    print("ba.length="+ba.length+", z.length="+z.length);
    assertneq( ba.length, z.length );
    print("First few bytes of z:");
    var li = [];
    for( i = 0; i < 5; ++i ) {
        li.push( z[i] );
    }
    print( JSON.stringify(li) );
    var u = z.gunzip();
    assert( u instanceof ByteArray );
    assert( !u.isGzipped, '!u.isGzipped' );
    print("Unzipped; u.length="+u.length);
    asserteq( ba.length, u.length );
    print("Unzipped data:\n"+u.stringValue());
    var z2 = ba.gzip();
    asserteq( z2.length, z.length );
    u.destroy();
    z.destroy();
    u = z2.gunzip();
    z2.destroy;
    asserteq( ba.length, u.length );
    ba.destroy();
    asserteq( origString===u.stringValue(), true );
    u.destroy();
}


test1();
testGZip();
print("If you made it this far without an exception then you win!");
