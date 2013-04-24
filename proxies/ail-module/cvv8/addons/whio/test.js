load('../test-common.js');

function testIODev()
{
    var d = new whio.IODev("/dev/null","r");

    assert( d instanceof whio.IODev, 'd is-a IODev' );
    assertThrows(function(){new whio.IODev(d,0);}, 'Invalid ctor args.');

    assert( /IODev/.test( d ), 'toString() appears to work.' );
    var s = new whio.Subdevice(d,10,50);
    assert( s instanceof whio.IODev, 's is-a IODev.' );
    assert( s instanceof whio.Subdevice, 's is-a Subdevice.' );
    assert( s.iomode(), 's.iomode() seems to work' );
    asserteq( 'function', typeof s.rebound, 's.rebound is-a function.');
    assertThrows( function(){d.rebound(1,"hi");},'Invalid arguments passed to rebound().');

    s.rebound(1,5);
    s.rebound(d,10,15);
    assert( s.close(), 's.close() seems to work' );

    assert( d.iomode(), 'd.iomode() seems to work' );
    assert( d.close(), 'd.close() seems to work' );
    assertThrows( function() {d.size();},
                  'Use after close() throws.');
}

function testOutStream()
{
    assertThrows(function(){new whio.OutStream(true);}, 'Invalid ctor args.');
    var d = new whio.OutStream("/dev/stdout",false);
    assert( d instanceof whio.OutStream, 'd is-a OutStream' );
    assert( d instanceof whio.StreamBase, 'd is-a StreamBase' );
    assert( /OutStream/.test( d ), 'toString() appears to work.' );

    asserteq( 10, d.write("hi, world\n"), 'write(String) seems to work.');

    var ba = new whio.ByteArray("hi, world\n");
    asserteq( ba.length, d.write(ba), 'write(ByteArray) seems to work.' );
    ba.destroy();

    assert( d.iomode(), 'd.iomode() seems to work' );
    d.flush();

    assert( d.close(), 'd.close() seems to work' );
    assertThrows( function() {d.flush();},
                  'Use after close() throws.');

}

function testMemoryDev() {
    var bSize = 1024*4;
    var d = new whio.MemoryIODev(bSize);
    asserteq( 0, d.size(), 'Initial size is 0.' );
    assert( d.bufferSize() >= bSize, 'Buffer size is as expected.' );
    assertThrows( function(){d.seek(1,7);},"seek()'s binding does very strict type/range checking.");
    assertThrows( function(){d.seek("1",whio.SEEK_SET);},"seek()'s binding does very strict type/range checking.");
    assert( 'number' === typeof whio.SEEK_SET, 'whio.SEEK_SET is-a number.');
    //s.seek(0,whio.SEEK_SET);
    asserteq( 1, d.seek(1,whio.SEEK_SET), "seek() works when we use whio.SEEK_XXX.");
    assert( d.close(), 'close() reports success.' );
    assertThrows( function(){d.write("a");}, 'Native "this" was both destroyed AND disconnected.');
}

function testInStream()
{
    var d = new whio.InStream("/etc/hosts");

    assert( d instanceof whio.InStream, 'd is-a InStream' );
    assert( d instanceof whio.StreamBase, 'd is-a StreamBase' );
    assert( /InStream/.test( d ), 'toString() appears to work.' );
    assertThrows(function(){new whio.InStream(true);}, 'Invalid ctor args.');
    assert( d.iomode(), 'd.iomode() seems to work' );

    var rdLen = 20;
    var got = d.read(rdLen,false);
    asserteq(rdLen, got.length);
    print("Read in ["+got+"]");
    got = d.read(rdLen,true);
    assert( got instanceof whio.ByteArray, 'Read in ByteArray.');
    asserteq(rdLen, got.length);
    print("Read in ["+got.stringValue()+"]");
    got.destroy();
    assert( d.close(), 'd.close() seems to work' );
    assertThrows( function() {d.iomode();},
                  'Use after close() throws.');
}

function testGZip()
{
    print("GZip tests...");
    var buf = new whio.MemoryIODev(1024*4);
    assert( buf instanceof whio.MemoryIODev, 'buf is-a MemoryIODev' );
    assert( buf instanceof whio.IODev, 'buf is-a IODev' );
    asserteq( 0, buf.size(), 'MemBuf initialize size problem has been solved.' );
    assert( buf.bufferSize() != 0, 'buf.bufferSize() == '+buf.bufferSize() );
    var src = new whio.InStream("/etc/hosts");
    src.gzipTo( buf );
    src.close();
    buf.seek(0,whio.SEEK_SET);
    assert( buf.size() > 0, 'Buffer grew.' );
    print("Compressed size = "+buf.size());

    src = new whio.InStream(buf,true);
    var dest = new whio.OutStream("/dev/stdout",false);
    var banner = '****************************************';
    print("DECOMPRESSED: "+banner);
    src.gunzipTo(dest);
    print("/DECOMPRESSED "+banner);
    src.close();
    dest.close();
}

function testEPFS()
{
    print("Testing EPFS...");
    print( "Version info: "+JSON.stringify(whio.EPFS.versionInfo) );
    var fname = "my.epfs";
    var opt = {
        inodeCount:10,
        blockSize:1024 * 8,
        maxBlocks:13
    };
    var fs = new whio.EPFS(fname,true,opt);
    var inodeCount = 0 /* number of inodes this test code allocates. */;
    assert( fs instanceof whio.EPFS, 'fs is-a EPFS.' );
    assert( /EPFS/.test( fs ), 'toString() appears to work.' );
    var fsOpt = fs.fsOptions();
    asserteq( fsOpt.inodeCount, opt.inodeCount );
    asserteq( fsOpt.maxBlocks, opt.maxBlocks );
    asserteq( fsOpt.blockSize, opt.blockSize );
    var label = "Test from JavaScript "+(new Date());
    assert( fs.label.maxLength > 0, 'fs.label.maxLength == '+fs.label.maxLength );
    fs.label(label);
    fs.installNamer("ht");
    ++inodeCount /* namer uses 1 inode. */;
    asserteq( fs.label(), label );
    
    var inodeId = 3;
    var d = fs.open(inodeId, whio.iomode.RWC);
    ++inodeCount;
    assert( d instanceof whio.EPFS.PseudoFile, 'd is-a whio.EPFS.PseudoFile' );
    assert( /PseudoFile/.test( d ), 'toString() appears to work.' );

    var hiMsg = "hi, world.";
    var msg = hiMsg;
    asserteq( msg.length, d.write(msg), 'PseudoFile.write() appears to work.' );
    asserteq( 0, d.seek(0,whio.SEEK_SET) );
    var gotMsg = d.read( msg.length, false );
    asserteq( gotMsg, msg );
    asserteq( inodeId, d.inodeId );
    assertThrows(function(){d.inodeId=42;},'Cannot set inodeId.');

    msg = 0xcafe;
    d.clientFlags = msg;
    asserteq( msg, d.clientFlags );

    msg = 6;
    d.mtime = msg;
    asserteq( msg, d.mtime );

    var pname = "my name";
    d.name = pname;
    asserteq( d.name, pname );

    if(1) {
        var infile = "test.js";
        var ist = new whio.InStream(infile);
        var zf = fs.open(infile+".gz",whio.iomode.RWC|whio.iomode.TRUNCATE);
        assert( zf instanceof whio.IODev, 'zf is-a IODev' );
        assert( zf instanceof whio.EPFS.PseudoFile, 'zf is-a PseudoFile' );
        ist.gzipTo(zf);
        print("Compressed "+infile+" to "+zf.size()+" bytes.");
        ist.close();
        zf.close();
        ++inodeCount;
    }
    
    assert( d.close(), 'PseudoFile.close() appears to work.' );
    assert( fs.close(), 'EPFS.close() appears to work.' );
    d = fs = null;
    
    if(1) { // re-open and read back some stuff...
	fs = new whio.EPFS(fname,false);
	assert( fs instanceof whio.EPFS, 'is-a EPFS' );

	d = fs.open( pname, whio.iomode.READ );
	assert( d instanceof whio.EPFS.PseudoFile, 'is-a PseudoFile' );
	assert( d instanceof whio.IODev, 'is-a IODev' );
	gotMsg = d.read( hiMsg.length, false );
	asserteq( hiMsg, gotMsg );
	assert( d.size() >= gotMsg.length, 'd.size() appears to work.' );
	d.close();

	var gotInodeCount = 0;
	fs.foreachInode( function(i) {
            print(JSON.stringify(i));
            ++gotInodeCount;
        });
	asserteq( inodeCount, gotInodeCount, 'Inode count matches expectations.' );
	fs.close();
    }
}

function testByteArrayDev()
{
    print("EXPERIMENTAL ByteArrayIODev tests...");
    var ba = new whio.ByteArray( 2000 );
    var d = new whio.ByteArrayIODev(ba,true);
    assert( whio.iomode.WRITE & d.iomode(), 'Opened in read/write mode.' );
    asserteq( ba.length, d.size(), 'ByteArray and dev are same size.' );
    asserteq( 3, d.write("hi!"), 'write() reported success.' );
    asserteq( ba[2], "!".charCodeAt(0), "write()n date landed in the ByteArray.");

    /** no workie: ByteArrayIODev::assertOpen() is never being called :(
        ba.length = 0;
        assertThrows( function(){d.flush();}, 'We expect the dev to notice the changed byte array.' );
    */
    d.close();
    ba.destroy();
}

try {
    testIODev();
    testOutStream();
    testInStream();
    testGZip();
    testEPFS();
    testMemoryDev();
    testByteArrayDev();
    print("If you got this far then it seems to work.");
}
catch(e) {
    print("EXCEPTION: "+e);
    for( var k in e ) {
        print(k+'='+e[k]);
    }
}
