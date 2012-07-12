
function test1()
{
    print("sleep() (and friends) tests...");
    print("For added variety, try tapping Ctrl-C while we're sleep()ing...");
    print("Sleeping a couple seconds...");
    var rc = sleep(2);
    print("Done. rc="+rc);
    print("wait()ing a little bit...");
    rc = mssleep(1500);
    print("Done. rc="+rc);
    print("Sleeping 0 seconds...");
    rc = sleep(0);
    print("Done. rc="+rc);
    
}

function test2()
{
    var b, e, i;
    var st = 800;
    var sl = mssleep;
    print("Looking for timing discrepancies due to how we (ab)use usleep()...");
    for( i = 0; i < 5; ++i )  {
        print("Sleeping "+st+" time unit(s)...");
        b = (new Date()).getTime();
        sl(st);
        e = (new Date()).getTime();
        print("Woke up.");
        print("Time diff: "+(e-b)+"ms");
    }    
}

function test3()
{
    load('MockTimer.js');
    var t = new MockTimer();
    var iv1 = 240;
    
    var e;
    t.setInterval( function() {
        print("Hit interval #1: "+iv1+'ms');
        }, iv1 );
    var iv2 = 500;
    t.setInterval( function() {
        print("Hit interval  #2: "+iv2+'ms');
        }, iv2);
    t.setTimeout( function() { print("One-shot event."); }, 799 );
    var duration = 1300;
    var precision = 100;
    var vtime = 0;
    var tickcount = 0;
    function beforeTick(timer) {
        e = (new Date()).getTime();
        vtime += precision;
        print("Tick #"+(++tickcount)+" at T+"+vtime+ " (real elapsed="+(e-b)+")");
        //return !((e-b) > duration);
        if( (e-b) > duration ) return false; //timer.stopBlockingTickLoop();
        return true;
    }
    print("Running tick loop with precision of "+precision+"ms for approximately "+duration+"ms...");
    var b = (new Date()).getTime();
    t.runBlockingTickLoop( precision, beforeTick );
    e = (new Date()).getTime();
    var diff = e-b;
    print("Done looping. Elapsed time: "+diff+"ms");
    print("Time overhead in addition to the requested "+duration+"ms: "+(diff-duration)+"ms ("+
        (100-(duration/diff*100))+"%)");
}

test1();
test2();
test3();
