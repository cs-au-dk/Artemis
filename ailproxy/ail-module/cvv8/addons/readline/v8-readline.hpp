#if !defined (V8_CONVERT_BYTEARRAY_H_INCLUDED)
#define V8_CONVERT_BYTEARRAY_H_INCLUDED
#include <v8.h>

namespace cvv8 {

    class Readline
    {
    public:
        static void SetupBindings( v8::Handle<v8::Object> dest );
    };
    
} // namespaces
#endif /* V8_CONVERT_BYTEARRAY_H_INCLUDED */
