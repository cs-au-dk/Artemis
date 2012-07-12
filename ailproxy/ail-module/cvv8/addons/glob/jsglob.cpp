/************************************************************************
Author: Stephan Beal (http://wanderinghorse.net/home/stephan)

License: New BSD

Based very heavily on:

http://code.google.com/p/v8cgi/source/browse/trunk/src/lib/socket/socket.cc

by Ondrej Zara


************************************************************************/
#if !defined _POSIX_SOURCE
#define _POSIX_SOURCE 1
#endif
#if !defined(_POSIX_C_SOURCE)
#define _POSIX_C_SOURCE 200112L
#endif


#include "whglob.h"
#include "jsglob.hpp"
#include <cvv8/invocable.hpp>



bool glob_matches( char const * pattern, char const * str )
{
    return (! pattern || !str )
        ? false
        : whglob_matches( pattern, str );
}

bool glob_matches_like( char const * pattern, char const * str, bool caseSensitive )
{
    return (!pattern || !str)
        ? false
        : whglob_matches_like( pattern, str, caseSensitive ? 1 : 0 );
}
bool glob_matches_like( char const * pattern, char const * str )
{
    return glob_matches_like( pattern, str, false );
}

void cvv8::SetupGlobBindings( v8::Handle<v8::Object> dest )
{
#define JSTR(X) v8::String::New(X)
#define SETF(K) dest->Set(JSTR(K), CastToJS(cb))
    v8::InvocationCallback cb;
    cb = FunctionToInCa<bool (char const *, char const *), glob_matches >::Call;
    SETF("matchesGlob");
    typedef FunctionToInCa<bool (char const *, char const *, bool), glob_matches_like > GML3;
    typedef FunctionToInCa<bool (char const *, char const *), glob_matches_like > GML2;
    typedef ArityDispatch< 2, GML2 > OML2;
    typedef ArityDispatch< 3, GML3, OML2 > OML3;
    cb = OML3::Call;
    SETF("matchesLike");
#undef SETF
#undef JSTR
}    

#undef CERR
