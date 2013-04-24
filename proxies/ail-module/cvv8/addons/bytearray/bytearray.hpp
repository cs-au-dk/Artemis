#if !defined (V8_CONVERT_BYTEARRAY_H_INCLUDED)
#define V8_CONVERT_BYTEARRAY_H_INCLUDED
#include <v8.h>

#include <cvv8/ClassCreator.hpp>
namespace cvv8 {

    class JSByteArray
    {
    public:
        typedef std::vector<unsigned char> BufferType;
    private:
        BufferType vec;
    public:
        /**
           Initializes an empty buffer.
        */
        JSByteArray()
            :vec()
        {
        }
        /**
           JS Usage:

           new ByteArray( [int length=0] )

           or:
           
           new ByteArray( string data [, int length=data.length] )

           or:
           
           new ByteArray( ByteArray data )

        */
        JSByteArray( v8::Handle<v8::Value> const & val, unsigned int len = 0 );

        ~JSByteArray();

        /** Returns the current length of the byte array. */
        uint32_t length() const
        {
            return this->vec.size();
        }
        /** Sets the length of the byte array. Throws if sz is "too
            long." Returns the new number of items. Any new entries (via
            growing the array) are filled with zeroes.
        */
        uint32_t length( uint32_t sz );

        /** toString() for JS. */
        std::string toString() const;    

        /**
           Returns array contents as a std::string.
        */
        std::string stringValue() const
        {
            return this->vec.empty()
                ? std::string()
                : std::string( this->vec.begin(), this->vec.end() );
        }


        /**
           Returns a pointer to the underlying raw buffer, or NULL
           if length() is 0. The pointer may be invalidated by
           any operation which changes this object's size or
           replaces the buffer (e.g. swapBuffer()).
        */
        void const * rawBuffer() const;
        /**
           With great power comes great responsibility.
        */
        void * rawBuffer();

        /**
           Adds the ByteArray class to the given destination object.

           JS API overview:

           Class name: ByteArray

           Ctors:

           ByteArray([int size=0])

           ByteArray(string data [, int length=data.length])

           Functions:

           toString() returns a string in the form "[object ByteArray...]".

           destroy() explicitly destroys all native data associated with the object.
           Further member calls on that JS reference will cause a JS-side exception
           to be triggered.
           
           Properties:

           .length = length, in bytes. Can be explicitly set to
           grow/shrink the buffer. When growing, new bytes are filled
           with zeroes.

           .stringValue (read-only) = the byte data as a
           string. Results are undefined if the data are not
           UTF8-encoded string data.


           Reminder to self: we don't pass the object handle by
           reference because that disallows implicit conversion from
           Handle<Function> to Handle<Object>, and we normally pass a
           JS constructor (Function handle) to this function.
        */
        static void SetupBindings( v8::Handle<v8::Object> dest );

        /**
           Swaps the internal buffer with the given one. This is
           really only in the public API to support the Socket API.
        */
        void swapBuffer( BufferType & buf );

        /**
            Appends len bytes from src to this object's buffer.
        */
        void append( void const * src, unsigned int len );
        /**
            Appends all bytes from other to this object's buffer, increasing
            the size if necessary.
        */
        void append( JSByteArray const & other );
        
        /**
            val must be one of (Number, String, ByteArray).
            
            A Number value is treated as a single byte value and is appended
            to this buffer. A String is treated as UTF-8 bytes and appended.
            A ByteArray is of course appended in the expected manner.
            
        */
        void append( v8::Handle<v8::Value> const & val );

        //     std::string asString() const;
        //     std::string asString( unsigned int fromOffset ) const;
        //     std::string asString( unsigned int fromOffset, unsigned int len ) const;


        int gzipTo( JSByteArray & dest, int level ) const;
        int gzipTo( JSByteArray & dest ) const;
        int gunzipTo( JSByteArray & dest ) const;

        /**
           Creates a new JSByteArray and calls gzipTo(*this,
           thatObject).  Throws if there is a binding-level error,
           returns v8::Null() if gzipping fails, or a handle to a new
           JSByteArray object on success. The new object contains the
           compressed data.
           
           The new object is owned by v8 and is theoretically not subject
           to garbage collection until the returned handle (and all subsequent
           references to it) goes out of scope.
        */
        v8::Handle<v8::Value> gzip() const;
        /**
           The converse of gzip(), this creates a new
           JSByteArray containing the decompressed version
           of this object.

           See gzip() for details about the return value.
        */
        v8::Handle<v8::Value> gunzip() const;

        /** Returns true if this object appears to contain
            gzipped data (we can only guess, though!).
        */
        bool isGzipped() const;
    private:
        static v8::Handle<v8::Value> indexedPropertyGetter(uint32_t index, const v8::AccessorInfo &info);
        static v8::Handle<v8::Value> indexedPropertySetter(uint32_t index, v8::Local< v8::Value > value, const v8::AccessorInfo &info);
        static v8::Handle<v8::Integer> indexedPropertyQuery(uint32_t index, const v8::AccessorInfo &info);
        static v8::Handle<v8::Boolean> indexedPropertyDeleter(uint32_t index, const v8::AccessorInfo &info);
        static v8::Handle<v8::Array> indexedPropertyEnumerator(const v8::AccessorInfo &info);

    };

    template <>
    struct TypeName< JSByteArray >
    {
        static char const * Value;
    };

    template <>
    class ClassCreator_Factory<JSByteArray>
    {
    public:
        typedef JSByteArray * ReturnType;
        static ReturnType Create( v8::Persistent<v8::Object> & jsSelf, v8::Arguments const & argv );
        static void Delete( JSByteArray * obj );
    };

    template <>
    struct JSToNative< JSByteArray > : JSToNative_ClassCreator< JSByteArray >
    {};

    
} // namespaces
#endif /* V8_CONVERT_BYTEARRAY_H_INCLUDED */
