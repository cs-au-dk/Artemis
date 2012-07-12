#if !defined (V8_CONVERT_TIME_HPP_INCLUDED)
#define V8_CONVERT_TIME_HPP_INCLUDED
#include <v8.h>

namespace cvv8 {
/**
    The 'time' namespace holds functions related to the passage of
    time, namely sleep(2)-like routines. Even though these are
    in the v8::convert namespace, they actually have no dependency
    on that library and can be dropped into arbitrary v8 clients
    (Unix-like ones, anyway).
*/    
namespace time {
    /**
        Installs the following functions into the given object, all 
        of which correspond to native v8::InvocationCallback 
        functions in this namespace:
        
        sleep(), mssleep(), usleep(), wait(), mswait(), uwait()
    */
    void SetupBindings( v8::Handle<v8::Object> dest );
    
    /**
       A sleep() implementation which can be bound to v8.
    
       JS usage: sleep(seconds)

       Behaves identically to the POSIX-standard sleep(), but returns
       -1 if argv[0] is not a positive integer.

       This routine uses v8::Unlocker to unlock the v8 engine for
       other threads.
       
       When built with C signals support, a signal-interrupted 
       sleep() call will cause a JS-side exception to be thrown. 
       When built without C signals support, a signal will probably 
       cause a crash.       

       If this function always returns -1 when when passing times of 
       1 second or larger, see this function's source code for a 
       compilation option (USLEEP_TOO_BEAUCOUP) which enables a 
       different code path as a workaround for such platforms. (That 
       also applies to all the other sleep()/wait() variants.)
    */
    v8::Handle<v8::Value> sleep(const v8::Arguments & argv);

    /**
       Like sleep(), but naps for the given number of milliseconds
       (thousandths of a second).
       
       JS Usage: msleep( milliseconds )
    */
    v8::Handle<v8::Value> mssleep(const v8::Arguments & argv);

    /**
       Like sleep(), but naps for the given number of microseconds
       (millionths of a second).
    
       JS Usage: usleep( microseconds )

       but be aware that you won't get really high resolution via JS
       when sleeping for very small intervals, due to the overhead involved
       in passing around JS params and locking/unlocking the engine.
       
    */
    v8::Handle<v8::Value> usleep(const v8::Arguments & argv);

    /**
       Identical to sleep(), but it does NOT unlock v8 while it's
       sleeping. Thus other threads cannot run while it is running.
    */
    v8::Handle<v8::Value> wait(const v8::Arguments & argv);

    /**
       Identical to mssleep(), but it does NOT unlock v8 while it's
       sleeping. Thus other threads cannot run while it is running.
    */
    v8::Handle<v8::Value> mswait(const v8::Arguments & argv);

    /**
       Identical to usleep(), but it does NOT unlock v8 while it's
       sleeping. Thus other threads cannot run while it is running.
    */
    v8::Handle<v8::Value> uwait(const v8::Arguments & argv);

}} // namespaces
#endif /* V8_CONVERT_TIME_HPP_INCLUDED */
