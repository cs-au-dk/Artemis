#if !defined(V8_CONVERT_SPRINTF_H_INCLUDED)
#define V8_CONVERT_SPRINTF_H_INCLUDED
#include <v8.h>

namespace cvv8 {

    /**
        Installs the sprintf() function in the given object.
    */
    void SetupJSPrintf( v8::Handle<v8::Object> dest );

    /**
        A v8::InvocationCallback implementation of sprintf(). It 
        works more or less like standard sprintf() but returns the 
        result as a string. It also has several formatting 
        extensions, like SQL escaping, URL (un)escaping, and minimal 
        HTML escaping. (These extensions may be disabled at 
        compile-time.)
        
        For the complete docs of the underlying native implementation,
        see:
        
        http://code.google.com/p/v8-juice/source/browse/trunk/src/lib/juice/whprintf.h
        
        But note that the %%z format option documented there is 
        disabled in this implementation.        
    */
    v8::Handle< v8::Value > sprintf( ::v8::Arguments const & argv );
}
#endif
