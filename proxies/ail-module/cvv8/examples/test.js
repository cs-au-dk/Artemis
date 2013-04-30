/**
   v8::convert test/demo app for use with v8-juice-shell (or compatible).
   To run it without v8-juice you need to remove the loadPlugin() call,
   build an app which includes the ConvertDemo.cpp code, and run this
   script through v8.

   Note that many of these tests/assertions depend on default state
   set in the demo app (ConvertDemo.cpp), and changing them there might
   (should) cause these tests to fail.
*/
load('../addons/test-common.js');

function printStackTrace(indention)
{
    var li = getStacktrace();
    if( li ) print('Stacktrace: '+JSON.stringify(li,0,indention));
}

function getCallLocation(framesBack){
    framesBack = (framesBack && (framesBack>0)) ? framesBack : 2;
    var li = getStacktrace(framesBack);
    if( !li ) return undefined;
    else return li[framesBack-1];
}


function test1()
{
    { // if these fail they'll probably cause an assertion in v8...
        BoundNative.testLocker();
        BoundNative.testLockerNoUnlocking()
    }

    var f = new BoundNative(42);
    print('f='+f);
    f.puts("hi, world");
    f.cputs("hi, world");
    f.doFoo();
    f.doFoo2(1,3.3);
    f.invoInt(1,2,3,4);
    f.doFooConst();
    f.nativeParam(f);
    if( f.runGC ) f.runGC();
    assertThrows( function() { f.throwStdString(); } );
    

    f.overloaded();
    f.overloaded(1);
    f.overloaded(2,3);
    //assertThrows( function() { f.overloaded(1,2,3); } );
    f.overloaded(1,2,3);
    // We set up f.publicIntRO to throw on write.
    assertThrows( function(){ f.publicIntRO = 1;} );

    /* Note the arguably unintuitive behaviour when incrementing
       f.publicIntRO: the return value of the ++ op is the incremented
       value, but we do not actually modify the underlying native int.
       This is v8's behaviour, not mine.
    */
    asserteq( ++f.publicIntRW, 43 );
    asserteq( f.publicIntRO, f.publicIntRW );

    ++f.publicStaticIntRW;
    asserteq( f.publicStaticIntRW, f.publicStaticIntRO );
    asserteq( ++f.publicStaticIntRO, 1+f.publicStaticIntRW );
    asserteq( f.publicStaticIntRW, f.publicStaticIntRO );
    asserteq( ++f.publicStaticIntRO, 1+f.publicStaticIntRW );
    asserteq( f.publicStaticIntRW, 43 );
    asserteq( f.publicStaticIntRO, f.publicStaticIntRW );
    asserteq('hi, world', f.message);
    asserteq('hi, world', f.staticString);
    f.staticString = 'hi';
    asserteq('hi', f.staticString);
    asserteq( f.sharedString2, f.staticStringRO );
    f.sharedString2 = "hi again";
    asserteq( f.sharedString2, f.staticStringRO );
    assertThrows( function(){ f.staticStringRO = 'bye';} );

    asserteq( typeof f.nsInt, 'number', 'f.nsInt is-a number.');
    f.nsInt = 7;
    asserteq( 8, ++f.nsInt );

    asserteq(42, f.answer);
    assert( /BoundNative/.test(f.toString()), 'toString() seems to work: '+f);

    asserteq( f.theInt, f.theIntNC );
    asserteq( ++f.theInt, f.theIntNC );
    asserteq( f.theInt, f.theIntNC );

    assertThrows( function(){ f.nativeParamRef(null); } );
    assertThrows( function(){ f.nativeParamConstRef(null); } );
    f.nativeParamRef(f);
    f.nativeParamConstRef(f);
    print("Return native pointer : "+f.nativeReturn());
    print("Return native const pointer : "+f.nativeReturnConst());
    print("Return native reference : "+f.nativeReturnRef());
    print("Return native const ref : "+f.nativeReturnConstRef());
    assert( !!f.self, '!!f.self' );
    assert( !!f.selfConst, '!!f.selfConst' );
    asserteq( f.self, f.selfConst );
    asserteq( f.selfRef, f.selfConst );
    asserteq( f.selfConstRef, f.self );
    assertThrows( function() { f.self = 'configured to throw when set.'; } );
    assertThrows( function() { f.selfConstRef = 'configured to throw when set.'; } );

    assertThrows( function(){ var x = f.throwingProperty;}, 'f.throwingProperty GETTER throws.' );
    assertThrows( function(){ f.throwingProperty = 3;}, 'f.throwingProperty SETTER throws.' );

    asserteq( 3, f.operatorLeftShift(3), 'f.operatorLeftShift() appears to work.');
    assert( f.destroy(), 'f.destroy() seems to work');
    assertThrows( function(){ f.doFoo();} );

    assertThrows( function() {
        new BoundNative(1,2,3,4,5,6);
    });

}

function test2()
{
    var s = new BoundSubNative();
    assert(s instanceof BoundNative, "BoundSubNative is-a BoundNative");
    print('s='+s);
    assert( /BoundSubNative/.test(s.toString()), 'toString() seems to work: '+s);
    asserteq( undefined, s.nonBoundNative(), 'Check native function returning (NonBoundType &).' );
    asserteq(true, s.destroy(), 's.destroy()');
}

function test3()
{
    function MySub()
    {
        this.prototype = this.__proto__ = new BoundSubNative();
    }
    //MySub.constructor.prototype = BoundSubNative;
    var m = new MySub();
    assert(m instanceof BoundNative,'m is-a BoundNative');
    assert(m instanceof BoundSubNative,'m is-a BoundSubNative');
    m.puts("Hi from JS-side subclass");
    assert( /BoundSubNative/.exec(m.toString()), 'toString() seems to work: '+m);
    assert(m.destroy(), 'm.destroy()');
    assertThrows( function() {m.doFoo();} );

}

function test4()
{
    if( ! BoundNative.prototype.runGC ) {
        print("runGC() not defined - skipping test.");
    }

    print("Creating several unreferenced objects and manually running GC...");
    var i =0;
    var max = 5;
    for( ; i < max; ++i ) {
        (i%2) ? new BoundSubNative() : new BoundNative();
    }
    for( i = 0; !BoundNative.prototype.runGC() && (i<max); ++i )
    {
        print("Waiting on GC to finish...");
        BoundNative.sleep(1);
    }
    if( max == i )
    {
        print("Gave up waiting after "+i+" iterations.");
    }
}

function testUnlockedFunctions()
{
    print("sleep()ing for a couple seconds... This 'might' unlock v8 while sleeping...");
    var b = (new Date()).getTime();
    BoundNative.sleep(2);
    var e = (new Date()).getTime();
    print("Done sleeping. Time elapsed: "+(e-b)+"ms");
}

function testPredicateOverloads()
{
    print("Testing out the experimental predicate-based overloading...");
    var b = new BoundSubNative();
    try {
        var rc;
        rc = b.bogo();
        asserteq( 0, rc );
        b.bogo(1 << 8);
        b.bogo(1 << 17);
        b.bogo((1<<31) * (1 << 10));
        b.bogo([1,2,3]);
        b.bogo({});
        b.bogo(1,"hi");
        b.bogo({},1,"hi");
        b.bogo(function(){
            // reminder: if we call b.bogo(arguments.callee)
            // from here we will crash with endless recursion.
            print("JS-side callback function. args from native world="+JSON.stringify(arguments));
        });
        var msg;
        msg = {a:1};
        rc = b.bogo( function(){print("FVF: argv[0]()");},
                     msg,
                     function(){print("FVF: argv[2]()");});
        asserteq( 'object', typeof rc );
        asserteq(msg,rc);

        msg = "(char const *)";
        rc = b.bogo( function(){print("FSF: argv[0]()");},
                     msg,
                     function(){print("FSF: argv[2]()");});
        asserteq( 'string', typeof rc );
        asserteq(msg, rc );

        assertThrows( function() { b.bogo(1,2,3,4,5,6); } );
    }
    finally { b.destroy(); }
}

function testMyType() {
    print("Testing constructor by-arity dispatcher...");
    assert( (new MyType()).destroy() );
    (new MyType("hi")).destroy();
    (new MyType(1,2.3)).destroy();
    (new MyType(1,2,3,4,5)).destroy();
    print("If you got this far, the ctor overloader worked.");
}

function testFunctors()
{
    var f = new BoundNative();
    assert( f.time > 0, 'f.time = '+f.time );
    assertThrows( function(){ f.time = 0;}, 'f.time disallows assignment.' );
    assert( f.myFunctor(), 'f.myFunctor()' );
    assert( f.myFunctor(3), 'f.myFunctor(int)' );
    asserteq( undefined, f.myFunctor(3.3), 'f.myFunctor(double)' );
    //assert( f.myFunctor(42), 'f.myFunctor(...)' );
    assertThrows( function(){ f.myFunctor(1,2);}, 'myFunctor() does not accept 2 arguments.' );
    f.destroy();
}

function testFork() {
    print("About to fork()...");
    assertThrows(function(){fork(1);},'fork() requires a Function argument.');
    fork(function(){
        print("This is a fork()'d process.");
    });
}

if(0) {
    /**
       Interesting: if we have a native handle in the global object
       then v8 is never GC'ing it, even if we dispose the context
       and run a V8::IdleNotification() loop. Hmmm. The problem
       would appear to be that the var we create keeps it alive,
       and that only destroying that var (e.g. assigning null to it)
       will will (theoretically) allow it to be released.
     */
    var originalBoundObject = new BoundNative();
    print("Created object which we hope to see cleaned up at app exit: "+originalBoundObject);
}

test1();
test2();
test3();
if( 0 && ('sleep' in BoundNative) && ('function' === typeof BoundNative.sleep) ) {
    test4();
    testUnlockedFunctions();
}
testPredicateOverloads()
if( ('MyType' in this) && ('function' === typeof this.MyType)) testMyType();
if(0) {
    try {
        asserteq(1,2,"Intentional error to check fetching of current line number.");
    }
    catch(e){
        print(e);
    }
    /** The line numbers printed out below should match the lines on which
        getCallLocation() is called. v8 uses 1-based rows/columns,
        by the way, not 1-based rows and 0-based columns as most editors do.
     */
    print( JSON.stringify(getCallLocation()) );
    print( JSON.stringify(getCallLocation()) );
    print( JSON.stringify(getCallLocation()) );
}
if( 'fork' in this ) testFork();
testFunctors();

print("Done!");
