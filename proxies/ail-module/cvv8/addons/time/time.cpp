/**
    Time/delay-related functions for v8.

    Requires unistd.h or a bit of hacking for the equivalent on
    non-Unix platforms.

    This code is intentionally kept free of library-level 
    dependencies (other than v8) so that it can easily be ported to 
    other v8-based projects.

    Author: Stephan Beal (http://wanderinghorse.net/home/stephan/)

    License: Public Domain
*/
#include <unistd.h> // sleep(), usleep()
#include "time.hpp"
#include <cerrno>
//#include <iostream> // only for debuggering
//#define CERR std::cerr << __FILE__ << ":" << std::dec << __LINE__ << " : "

#define USE_SIGNALS 1
#if USE_SIGNALS
#include <signal.h>
#endif
namespace cvv8 { namespace time {
    namespace Detail
    {
        /**
           A sentry type to set a no-op signal handler for certain signals
           for its lifetime.  When it destructs, it restores the original
           signal handler.

           Re-maps the following signals: SIGINT, SIGPIPE
           
           The purpose of this is to allow low-level calls like ::accept()
           and ::bind() to fail with a EINTR when interrupted, instead of
           having the signal handler kill the app.

           FIXME: check into using sigprocmask() instead of signal()
           internally.
        */
        struct CSignalSentry
        {
#if USE_SIGNALS
            static void signal_ignore(int)
            {
                /*
                  If i don't install a signal handler, ctrl-c (SIGINT)
                  kills my app violently during interrupted ops, as would be expected. If
                  i do install a handler then those ops returns with errno=EINTR.
                */
                //JSTOSS(v8::String::New("C signal caught!"));
            }
            sighandler_t oldInt;
            sighandler_t oldPipe;
            CSignalSentry()
                : oldInt(signal(SIGINT, signal_ignore)),
                  oldPipe(signal(SIGPIPE, signal_ignore))
            {
            }
            ~CSignalSentry()
            {
                signal( SIGINT, oldInt );
                signal( SIGPIPE, oldPipe );
            }
#else
            CSignalSentry() {}
            ~CSignalSentry(){}
#endif /*USE_SIGNALS*/
        };
        /**
           Internal helper type to compile-time select whether or not
           to yield the thread to v8 during a sleep-like function.
        */
        template <bool IsLockable>
        struct SleepUnlocker
        {
            SleepUnlocker(){}
            ~SleepUnlocker(){}
            v8::Unlocker proxy;
#if USE_SIGNALS
            CSignalSentry sig;
#endif
        };
        template <>
        struct SleepUnlocker<false>
        {
            SleepUnlocker(){}
            ~SleepUnlocker(){}
#if USE_SIGNALS
            CSignalSentry sig;
#endif
        };

        /**
            Internal impl of sleep()/mssleep()/usleep() and
            wait()/mswait()/uwait().
            
            DelayMult must be:

            sleep/wait(): 1000*1000
            mssleep/mswait(): 1000
            usleep/uwait(): 1

            useLocker: if it is true then v8::Unlocker is used to give
            thread control back to v8 for the duration of the sleep. If it
            is false then the current locker is not yielded.

            The return value will be the return value of ::usleep(),
            or -1 if argv[0] is less than 0. A value of 0 will also
            cause a sleep, which will have the side effect of briefly
            unlocking v8 if useLocker is true. Thus a sleep value of 0
            can be used to implement a "yield" operation.

            TODO(?): come up with some semantics which allow the caller 
            to know if the sleep was interrupted by a signal 
            (potentially non-fatal, like a timeout).

            Pedantic Achtung: POSIX has obsoleted usleep() and 
            recommends nanonosleep(), with its more complicated 
            interface. OTOH, according to APUE, nanosleep() is only 
            required to be defined on platforms which implement "the 
            real-time extensions". What to do?
        */
        template <uint32_t DelayMult, bool useLocker>
        static v8::Handle<v8::Value> sleepImpl(const v8::Arguments& argv)
        {
            int32_t st = argv.Length() ? argv[0]->Int32Value() : -1;
            int rc = -1;
            if(0 <= st)
            {
/** Set USLEEP_TOO_BEAUCOUP to a true value if your platform's usleep()
    does not like values >=1 second.
*/
#if !defined(USLEEP_TOO_BEAUCOUP)
#  define USLEEP_TOO_BEAUCOUP 0
#endif
#if USLEEP_TOO_BEAUCOUP 
                /**
                    According to my man pages, usleep() doesn't 
                    really want to be given a value >= 1000000. So 
                    we cheat a bit and call ::usleep() in increments 
                    of the largest value it portably accepts. This 
                    of course has (hopefully negligible) 
                    side-effects on the overall sleep time when the 
                    client passes values >= 1 second.
                */
                uint32_t left = static_cast<uint32_t>(st) * DelayMult;
                static uint32_t const step = 999999;
                uint32_t t = 0;
                typedef Detail::SleepUnlocker<useLocker> SU;
                SU const ul;
                while( true )
                {
                    if( left >= step )
                    {
                        left -= step;
                        t = step;
                    }
                    else
                    {
                        t = left;
                    }
                    //if( t <= 100 /*arbitrary!*/ ) break;// highly arguable
                    errno = 0;
                    rc = ::usleep( t );
#    if USE_SIGNALS
                    if( EINTR == errno )
                    {
                        return v8::ThrowException(v8::Exception::Error(v8::String::New("Sleep time was interruped by a C signal.")));
                    }
#    endif // USE_SIGNALS
                    if( t == left ) break;
                }
#else // assume usleep() can handle values >= 1 second...
                typedef Detail::SleepUnlocker<useLocker> SU;
                SU const ul;
                errno = 0;
                rc = ::usleep( static_cast<uint32_t>(st) * DelayMult );
#    if USE_SIGNALS
                if( EINTR == errno )
                {
                    return v8::ThrowException(v8::Exception::Error(v8::String::New("Sleep time was interruped by a C signal.")));
                }
#    endif // USE_SIGNALS
#endif /* USLEEP_TOO_BEAUCOUP */
#undef USLEEP_TOO_BEAUCOUP
            }
            return v8::Integer::New(rc);
        }

    }

    v8::Handle<v8::Value> sleep(const v8::Arguments& argv)
    {
        return Detail::sleepImpl<1000*1000,true>( argv );
    }

    v8::Handle<v8::Value> mssleep(const v8::Arguments& argv)
    {
        return Detail::sleepImpl<1000,true>( argv );
    }

    v8::Handle<v8::Value> usleep(const v8::Arguments& argv)
    {
        return Detail::sleepImpl<1,true>( argv );
    }
    

    v8::Handle<v8::Value> wait(const v8::Arguments& argv)
    {
        return Detail::sleepImpl<1000*1000,false>( argv );
    }

    v8::Handle<v8::Value> mswait(const v8::Arguments& argv)
    {
        return Detail::sleepImpl<1000,false>( argv );
    }

    v8::Handle<v8::Value> uwait(const v8::Arguments& argv)
    {
        return Detail::sleepImpl<1,false>( argv );
    }

    void SetupBindings( v8::Handle<v8::Object> dest )
    {
#define SET(F) dest->Set(v8::String::New(#F), v8::FunctionTemplate::New(F)->GetFunction())
        SET(sleep);
        SET(mssleep);
        SET(usleep);
        SET(wait);
        SET(mswait);
        SET(uwait);
#undef SET        
    }

}} // namespaces

#undef USE_SIGNALS
