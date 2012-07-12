/**

Mock Timers: platform-neutral implementations of setTimeout(),
clearTimeout(), and friends.

This class provides the significant features of standards-conforming
setTimeout() (and friends), but leaves the "passage of time" parts
to the client. See the tick() member for how that works.

This code is a direct derivative of:

http://github.com/visionmedia/js-mock-timers/blob/master/lib/timers.js

(Version 1.0.2, git ID e5d1a122c50151296282e771beb55cdb23c02d11)

Copyright TJ Holowaychuk <tj@vision-media.ca> (MIT Licensed)

This copy has been hacked significanty by Stephan Beal
(http://wanderinghorse.net/home/stephan/). Changes include:

- Encapsulated the core features in a class.

- Added semicolons to the end of all statements. JS doesn't require
this but not having them breaks code minifiers and
accidentally-reformatted code can have its logic inadvertently
changed.

- Documented the important parts of the API.
*/
function MockTimer()
{
    this.resetTimers();
    this.propagateTimerExceptions = true;
    return this;
};
/**
   Private implementation of clearInterval() and setInterval().
   Removes the timer with the given _id_.

   @param  {int} id
   @return {bool}
   @api private
*/
MockTimer.prototype.clearIntervalImpl = function(id)
{
    return delete this.timers[--id]
};

/**
 * Localized timer stack.
 */
MockTimer.prototype.timers = [];
  
/**
   Set mock timeout with _callback_ and timeout of _ms_.

   See tick() for more information.

   @param  {function} callback
   @param  {int} ms
   @return {int}
   @api public
*/
MockTimer.prototype.setTimeout = function(callback, ms)
{
    /**
    BUG:
    
    We "should" implement setInterval() in terms of setTimeout(),
    as opposed to the other way around, but the callback.mock
    value injected by setInterval() interferes with that.
    
    Because of that, if the timeout value is smaller than the
    the value passed to tick() then the callback might be called
    multiple times.
    */
    var id;
    var self = this;
    var cb = function(){
        self.clearInterval(id);
        callback();
    };
    id = this.setInterval( cb, ms);
    cb.mock.isInterval = false /* ugly kludge */;
    return id;
};
/**
 * Set mock interval with _callback_ and interval of _ms_.
 *
 * Bug: for internal reasons, callback must be an anonymous function,
   or otherwise must not be passed multiple times to this function.
   
 * @param  {function} callback
 * @param  {int} ms
 * @return {int}
 * @api public
 */
MockTimer.prototype.setInterval = function(callback, ms)
{
    /*
        Reminder: this 'mock' bit is part of the original impl. It works
        fine with anonymous functions but will not work property if callback
        is a function handle passed multiple times to this function.
    */
    callback.mock = {step:ms, current:0,last:0,isInterval:true/* ugly kludge */};
    //callback.step = ms, callback.current = callback.last = 0;
    return this.timers[this.timers.length] = callback, this.timers.length;
};
/**
   Expects arguments[0] to be a timer ID which was returned from
   setTimeout() or setInterval(). If it is, it is removed from the
   timer queue, such that it will not be fired the next time its timer
   would normally have triggered.

   A setTimeout() handler is only called once, but clearing it will
   keep it from firing (if it is cleared in time, of course).
*/
MockTimer.prototype.clearTimeout = MockTimer.prototype.clearIntervalImpl;
/** Identical to clearTimeout(). */
MockTimer.prototype.clearInterval = MockTimer.prototype.clearIntervalImpl;
/**
 * Reset timers. All existing timers added via setTimeout() and setInterval()
 * are removed from the timer queue.
 *
 * @return empty {array}
 * @api public
 */
MockTimer.prototype.resetTimers = function()
{
    return this.timers = [];
};
/**
  Increment each timer's internal clock by _ms_. If a given timer's
  "time has come", its callback is called. A callback may be called
  multiple times in one tick() if its interval is smaller than the
  tick increment and it needs to "catch up". Thus events are not
  "lost" by a long tick, but may be run in very rapid order
  when catching up.

  Clients running on platforms which have their own thread-like
  support (or at least a sleep()-like function) can create functions
  which call tick() at specific intervals. Without such a loop, the
  passage of time for the timers is very relative. e.g. 20 real
  minutes might pass between calls, but the timers only react to the
  time spans which are incrementally passed to this function.

  Exceptions thrown by callbacks are silently ignored if this.propagateTimerExceptions
  is false. Its default value is true, in which case thrown exceptions
  are propagated.

  @param  {int} ms
  @api public
*/
MockTimer.prototype.tick = function(ms)
{
    var tm = this.timers;
    for (var i = 0, len = tm.length; i < len; ++i)
    {
        var it = tm[i];
        //var mo = it.mock; // weird: i hold a reference to tm[i].mock i can get segfaults at app exit
        if (it && (it.mock.current += ms))
        {
            if (it.mock.current - it.mock.last >= it.mock.step) {
                var times = it.mock.isInterval ? /* ugly kludge to avoid calling non-internals multiple times */
                        Math.floor((it.mock.current - it.mock.last) / it.mock.step) :
                        1;
                var remainder = (it.mock.current - it.mock.last) % it.mock.step;
                it.mock.last = it.mock.current - remainder;
                //if( ! it.mock.isInterval ) times = 1;
                try
                {
                    while (times-- && it) it();
                }
                catch(e){ if(this.propagateTimerExceptions) throw e; }
            }
        }
    }
};

/**
   Requires libv8-juice-specific functionality.

   This enters a mail event loop, running every intervalMS
   milliseconds (insofar as the JS VM threading features allow us
   to).

   Each intervalMS ms, this.tick(intervalMS) is called. The wait
   is achieved by sleep()ing for intervalMS ms. The various
   v8-juice sleep() implementations explicitly unlock the v8 VM
   during the sleep, giving other threads some time to work.

   If beforeTick is-a function, it is called like:

   beforeTick( this, intervalMS )

   after sleeping but before any timer callbacks are checked or 
   triggered. If beforeTick() returns a true value then the 
   up-coming tick() is called, otherwise tick() is not called and 
   this function returns. If it calls stopBlockingTickLoop() on the 
   timer object then the up-coming tick() is _not_ fired and looping 
   stops at the earliest possible opportunity.

   If beforeTick() throw an exception it is propagated back to the
   caller.  If a timer callback throws an exception, it will be
   propagated back only if this.propagateTimerExceptions is true,
   otherwise exceptions from timer callbacks are silently ignored.

   This function does not return until one of the following:
   
   a) it propagates an exception
   
   b) beforeTick() returns a false value.
   
   c) some code asynchronously (or in beforeTick()) calls
   stopBlockingTickLoop() on this timer object.
*/
MockTimer.prototype.runBlockingTickLoop = function( intervalMS, beforeTick )
{
    if( this.loopInfo )
    {
        throw new Error( "MockTimer.startTickLoop() must only be called once!" );
        return false;
    }
    if( ! arguments.length || !arguments[0] )
    {
        intervalMS = MockTimer.defaultLoopInterval;
    }
    var loopInfo = this.loopInfo = {
        ms:0+intervalMS,
        stopBlockingTickLoop:false
    };
    var callBefore = beforeTick instanceof Function;
    var check;
    while(true)
    {
        mssleep( loopInfo.ms );
        if( loopInfo.stopBlockingTickLoop ) break;
        else if( callBefore ) {
            try {
                check = loopInfo;
                check = beforeTick(this,loopInfo.ms)
                if( ! check ) break;
                if( loopInfo.stopBlockingTickLoop ) break /* check again after beforeTick()!*/;
            }
            finally {
                if( check === loopInfo ) delete this.loopInfo /* we're in a propagating exception */;
            }
            // if not propagating, fall through...
        }
        this.tick( loopInfo.ms );
    };
    return this;
};
/**
    Can be called to tell runBlockingTickLoop() to stop
    looping the next chance it gets.
    
    This function has no side-effects if the loop is not
    running.
*/
MockTimer.prototype.stopBlockingTickLoop = function()
{
    return this.loopInfo ?
        this.loopInfo.stopBlockingTickLoop = true :
        false;
};

/**
   Requires a standards-conformant (or mostly-so) implementations
   of setTimeout() and clearTimeout().

   Starts an interval timer which calls this.tick(intervalMS)
   every intervalMS milliseconds, using setInterval() for the
   interlying looping. If beforeTick is-a function then
   beforeTick(intervalMS) is called just before every call to
   this.tick().

   Any current and previous timers created via this.setTimeout()
   or this.setInterval() will be triggered using their own timing
   intervals, but only insofar as the granularity of intervalMS
   allows them to do so. If intervalMS is larger than any of the
   timers' intervals, then such timers may be called multiple
   times in immediate succession to "catch up". See tick() for
   details.

   The library-wide default value for intervalMS is defined as
   MockTimer.defaultLoopInterval, and that
   default is used if no arguments are passed in or if
   !intervalMS.

   If intervalMS is very small, this loop will require
   appropriately more runtime.

   Returns this object on success.

   It is illegal to call startAsyncLoop_setInterval() more than once
   without a subsequent call to this.stopAsyncLoop_setInterval()
   between the calls. Doing so will cause this function to throw an
   exception.

   After calling this, this.stopAsyncLoop() is an alias for
   this.stopAsyncLoop_setInterval().
*/
MockTimer.prototype.startAsyncLoop_setInterval = function( intervalMS, beforeTick )
{
    if( this.loopInfo )
    {
        throw new Error( "MockTimer.startAsyncLoop_setInterval() must only be called once!" );
        return false;
    }
    if( ! arguments.length || !arguments[0] )
    {
        intervalMS = MockTimer.defaultLoopInterval;
    }
    var loopInfo = { ms:0+intervalMS };
    this.loopInfo = loopInfo;
    var self = this;
    this.stopAsyncLoop = this.stopAsyncLoop_setInterval;
    loopInfo.timerID = setInterval( function()
                                    {
                                        if( beforeTick instanceof Function )
                                        {
                                            beforeTick(loopInfo.ms);
                                        }
                                        self.tick(loopInfo.ms);
                                    },
                                    loopInfo.ms );
    return this;
};
/**
   Stops the startAsyncLoop_setInterval() loop. By default it also clears
   all timers, but if passed the explicit boolean value
   false (i.e. false===arguments[0]) then it will not clear
   the timeouts. They will not be run, but they can be
   started again by calling startAsyncLoop_setInterval() again.
*/
MockTimer.prototype.stopAsyncLoop_setInterval = function()
{
    if( ! this.loopInfo || ! this.loopInfo.timerID )
    {
        throw new Error( "MockTimer.startAsyncLoop_setInterval() is not running!" );
        return false;
    }
    clearInterval( this.loopInfo.timerID );
    if( !arguments.length || (false!==arguments[0]) )
    {
        this.resetTimers();
    }
    this.loopInfo.timerID = 0;
    //this.loopInfo = undefined;
    //delete this.loopInfo;
    return this;
};

/** Defines the library-wide default interval value (in milliseconds) for various
    timer-looping implementations. */
MockTimer.defaultLoopInterval = 200;

       
/* Test/debug code. */
if(0) (function(){
           function timestamp()
           {
               var t =  (new Date()).getTime();
               var rc = t + ' (+'
                   +( t - arguments.callee.prev )
                   +'): '
                   ;
               arguments.callee.prev = t;
               return rc;
           }
           timestamp.prev = (new Date()).getTime();
           
           MockTimer.test1 = function()
           {
               var pt = new MockTimer();
               function one()
               {
                   print("one()");
               }
               function labelFunc(s)
               {
                   return function(){ print(s); };
               }

               var t = pt.setInterval( labelFunc("Hi!"), 3 );
               var i;
               var tick = 1;
               for( i = 0; i < 10; ++i )
               {
                   print( i );
                   pt.tick( tick );
               }
           };

           MockTimer.test2 = function()
           {
               print("Non-blocking-loop tests...");
               var pt = new MockTimer();
               var countdown = 10;
               pt.runCount = 0;
               function labelFunc(s)
               {
                   var msg = s;
                   return function(){
                       --countdown;
                       if( countdown == 0 )
                       {
                           pt.clearInterval( pt.myID );
                       }
                       if( countdown > 0 )
                       {
                           print(countdown, timestamp(),++pt.runCount,':',msg);
                       }
                       else
                       {
                           // we were just cleared or we are remnant timers.
                       }
                       return countdown > 0;
                   };
               }
               var timerRes = 100;
               pt.myID = pt.startAsyncLoop_JuiceThread( timerRes, function() {
                                     //print('tick...');
                                 } );
               pt.ms = 300;
               pt.setInterval( labelFunc("tock!"), pt.ms );
               print("setInterval(",pt.ms,") =",pt.myID,', timer resolution =',timerRes);
               var sltms = pt.ms*2;
               for( ; countdown > 0; ) {
                   print('... main thread waiting',sltms+'ms, still awaiting',countdown,' timer run(s) ...');
                   mssleep(sltms); // if we don't sleep, the interval threads get blocked
               }
               pt.stopAsyncLoop_JuiceThread();
               print('Main thread done.');
           };

           MockTimer.test3 = function()
           {
               print("Blocking-loop tests...");
               var pt = new MockTimer();
               pt.runCount = 0;
               var countdown = 10;
               function labelFunc(s)
               {
                   var msg = s;
                   return function(mock,ms){
                       if( ! mock && (countdown>0))
                       { /* interval mode */
                           if( ! --countdown ) pt.clearInterval( pt.myID );
                           print(countdown, timestamp(), ++pt.runCount,':',msg);
                           return countdown > 0;
                       }
                       else /* beforeTick() mode */
                       {
                           print(countdown, timestamp(),':',msg);
                           return countdown > 0;
                       }
                   };
               }
               var timerRes = 500;
               pt.ms = 800;
               pt.myID = pt.setInterval( labelFunc("tock!"), pt.ms );
               print("setInterval(",pt.ms,") =",pt.myID,', timer resolution =',timerRes);
               print("Entering blocking loop...");
               pt.runBlockingTickLoop( timerRes, labelFunc("tick!") );
               print("blocking loop done.");
           };

           if( 1 && ('v8JuiceVersion' in this /* == is v8-juice-shell or v8::juice::JuiceShell client*/) )
           {
               //MockTimer.test1();
               MockTimer.test2();
               MockTimer.test3();
               //sleep(3);
           }
})();
