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

#include "bytearray.hpp"

#if !defined(ByteArray_CONFIG_ENABLE_ZLIB)
#  if defined(_WIN32) || defined(_WIN64)
#    define ByteArray_CONFIG_ENABLE_ZLIB 0
#  else
#    define ByteArray_CONFIG_ENABLE_ZLIB 1
#  endif
#endif

#include <cvv8/convert.hpp>
#include <cvv8/properties.hpp>
#include <cvv8/XTo.hpp>

#include <sstream>
#include <vector>
#include <string.h> /* memset */
#if ByteArray_CONFIG_ENABLE_ZLIB
#  include <zlib.h>
#endif



#if 1 && !defined(CERR)
#include <iostream> /* only for debuggering */
#define CERR std::cerr << __FILE__ << ":" << std::dec << __LINE__ << " : "
#endif

namespace cv = cvv8;
#define JSTR(X) v8::String::New(X)
using cv::JSByteArray;


#define BA_JS_CLASS_NAME "ByteArray"

namespace cvv8 {
    char const * TypeName<JSByteArray>::Value = BA_JS_CLASS_NAME;

    //! Internal impl of JSByteArray::gzipTo().
    static int GZipJSByteArray( JSByteArray const & src, JSByteArray & dest, int level = 3 );
    //! Internal impl of JSByteArray::gunzipTo().
    static int GUnzipJSByteArray( JSByteArray const & src, JSByteArray & dest );

    
    JSByteArray * ClassCreator_Factory<JSByteArray>::Create( v8::Persistent<v8::Object> & jsSelf, v8::Arguments const & argv )
    {
        int const argc  = argv.Length();
        JSByteArray * ba = NULL;
        if(1==argc)
        {
            ba = new JSByteArray( argv[0] );
        }
        else if( 2 == argc )
        {
            ba = new JSByteArray( argv[0], cv::CastFromJS<unsigned int>(argv[1]) );
        }
        else if( ! argc )
        {
            ba = new JSByteArray();
        }
        if( !ba )
        {
            throw std::runtime_error("Could not create new JS-side "BA_JS_CLASS_NAME" instance.");
        }
        return ba;
    }

    void ClassCreator_Factory<JSByteArray>::Delete( JSByteArray * obj )
    {
        delete obj;
    }
    
} // cvv8


namespace {
    bool enableDestructorDebug = false;
    
    void setEnableDestructorDebug( bool b )
    {
        enableDestructorDebug = b;
    }
}
/************************************************************************
   Down here is where the runtime setup parts of the bindings take place...
************************************************************************/
JSByteArray::~JSByteArray()
{
    if( enableDestructorDebug )
    {
        CERR << "Destructing native JSByteArray@"<<(void const *)this<<'\n';
    }
}

JSByteArray::JSByteArray( v8::Handle<v8::Value> const & val, unsigned int len )
    : vec()
{
    if( !val.IsEmpty()
        && !val->IsNull()
        && !val->IsUndefined()
        )
    {
        
        if( val->IsNumber() )
        {
            const int32_t x = cv::JSToInt32( val );
            if( x < 0 )
            {
                std::ostringstream msg;
                msg << TypeName<JSByteArray>::Value
                    << " ctor argument may not be a negative number.";
                throw std::runtime_error( msg.str().c_str() );
            }
            this->length( (unsigned int)x );
            return;
        }
        else if( val->IsObject() )
        { // TODO: honor len here.
            JSByteArray * other = CastFromJS<JSByteArray>(val);
            if( other )
            {
                this->append( *other );
                return;
            }
            else
            {
                std::ostringstream msg;
                msg << TypeName<JSByteArray>::Value
                    << " ctor argument is not a "<<TypeName<JSByteArray>::Value<<" object.";
                throw std::range_error( msg.str().c_str() );
            }
        }
        else
        {
            std::string const & x( cv::JSToStdString( val ) );
            if( ! len ) len = x.size();
            if( len > x.size() ) len = x.size();
            if( len )
            {
                this->length( len );
                this->vec.assign( x.begin(), x.end() );
            }
            return;
        }
    }
}

void JSByteArray::swapBuffer( BufferType & buf )
{
    this->vec.swap(buf);
}

v8::Handle<v8::Value> JSByteArray::indexedPropertyGetter(uint32_t index, const v8::AccessorInfo &info)
{
    //CERR << "indexed getter: "<<index<<'\n';
    JSByteArray * ar = cv::CastFromJS<JSByteArray*>( info.This() );
    if( ! ar ) return v8::ThrowException(JSTR("Native 'this' not found!"));
    if( index >= ar->length() ) return v8::Undefined();
    else
    {
        return cv::CastToJS<int>( ar->vec[index] );
    }
}

v8::Handle<v8::Value> JSByteArray::indexedPropertySetter(uint32_t index, v8::Local< v8::Value > value, const v8::AccessorInfo &info)
{
    //CERR << "indexed setter: "<<index<<'\n';
    v8::Handle<v8::Value> rv;
    JSByteArray * ar = cv::CastFromJS<JSByteArray*>( info.This() );
    if( ! ar ) return v8::ThrowException(JSTR("Native 'this' not found!"));
#if 0
    if( index >= ar->length() )
    {
        ar->length( index+1 );
        //CERR << "capacity = "<<ar->vec.capacity()<<'\n';
        //CERR << "size = "<<ar->vec.size()<<'\n';
    }
#endif
    if( index >= ar->length() )
    {
#if 1
        cv::StringBuffer msg;
        msg << "Index "<<index<<" is out of bounds for "
            <<TypeName<JSByteArray>::Value
            << " of length "<<ar->length()<<'!';
        return v8::ThrowException(msg);
#else
        return rv;
#endif
    }
    else
    {
        // reminder: we don't convert as uint8_t due to collisions with char/int8_t.
        int32_t const ival = value->Int32Value()
            /* when is Apple going to get around to trademarking iNt32_t? */
        ;
        if( (ival < 0) || (ival > 255) )
        {
            cv::StringBuffer msg;
            msg << "Byte value "<<ival<<" is out of range. It must be between 0 and 255, inclusive.";
            return v8::ThrowException(msg.toError());
        }
        return cv::CastToJS<uint16_t>( ar->vec[index] = (unsigned char)(ival & 0xff) );
    }
}

v8::Handle<v8::Integer> JSByteArray::indexedPropertyQuery(uint32_t index, const v8::AccessorInfo &info)
{
    //CERR << "indexed query "<<index<<'\n';
    JSByteArray * ar = cv::CastFromJS<JSByteArray*>( info.This() );
    if( ! ar ) return v8::Handle<v8::Integer>();
    else
    {
#if 0
        return (index < ar->length())
            ? v8::True()
            : v8::False()
            ;
#else
        return v8::Integer::New(0);
        /*
          The return type of this function changed from Boolean
          sometime in 2010 and the bastards didn't document what the
          new semantics are. They write only that the integer "encodes
          information about the property." Poking around in v8's
          sources seems to imply that any non-empty integer handle is
          treated as "true" here.
         */
#endif
    }
}
v8::Handle<v8::Boolean> JSByteArray::indexedPropertyDeleter(uint32_t index, const v8::AccessorInfo &info)
{
    //CERR << "indexed deleter "<<index<<'\n';
    //CERR << "marker!\n";
    return v8::False();
}
v8::Handle<v8::Array> JSByteArray::indexedPropertyEnumerator(const v8::AccessorInfo &info)
{
    //CERR << "indexed enumerator\n";
    v8::Handle<v8::Array> rv;
    JSByteArray * ar = cv::CastFromJS<JSByteArray*>( info.This() );
    if( ! ar )
    {
        v8::ThrowException(JSTR("Native 'this' not found!"));
        return rv;
    }
    rv = v8::Handle<v8::Array>( v8::Array::New(ar->length()) );
    for( uint32_t i = 0; i < ar->length(); ++i )
    {
        rv->Set( i, cv::CastToJS(i) );
    }
    return rv;
}
std::string JSByteArray::toString() const
{
    std::ostringstream os;
    os << "[object "
       << TypeName<JSByteArray>::Value
       << "@"<<(void const *)this
       << ", length="<<this->length()
       << ']';
    return os.str();
}
bool JSByteArray::isGzipped() const
{
    if( this->vec.empty() || (19 >= this->vec.size()) ) return false
        /* smallest gzip file i've seen was 20 bytes, from a 0-byte file. */
        ;
    else
    {
        unsigned char const * mem = (unsigned char const *)this->rawBuffer();
        return (31 == mem[0]) && (139 == mem[1]);
    }
}

void * JSByteArray::rawBuffer()
{
    return this->vec.empty()
        ? NULL
        : &this->vec[0];
}

void const * JSByteArray::rawBuffer() const
{
    return this->vec.empty()
        ? NULL
        : &this->vec[0];
}

uint32_t JSByteArray::length( uint32_t sz )
{
    if( sz > this->vec.max_size() )
    {
        cv::StringBuffer msg;
        msg << TypeName<JSByteArray>::Value
            << " length "<<sz << " is too large to store "
            << "in std::vector! Max size is "<< this->vec.max_size()<<".";
        throw std::runtime_error( msg.Content().c_str() );
    }
    if( sz != this->vec.size() )
    {
        if( ! this->vec.empty() )
        {
            v8::V8::AdjustAmountOfExternalAllocatedMemory( - static_cast<int>(this->vec.size()) );
        }
        this->vec.resize(sz,0);
        v8::V8::AdjustAmountOfExternalAllocatedMemory( static_cast<int>(this->vec.size()) );
    }
    return this->vec.size();
}

void JSByteArray::append( void const * src, unsigned int len )
{
    if( ! src || !len ) return;
    size_t const newLen = this->length() + len;
    this->vec.reserve( newLen );
    unsigned char const * beg = (unsigned char const *)src;
    std::copy( beg, beg + len, std::back_inserter(this->vec) );
}
void JSByteArray::append( JSByteArray const & other )
{
    std::copy( other.vec.begin(), other.vec.end(), std::back_inserter(this->vec) );
}


void JSByteArray::append( v8::Handle<v8::Value> const & val )
{
    if( val->IsString() )
    {
        v8::String::Utf8Value asc(val);
        this->append( *asc, static_cast<unsigned int>(asc.length()) );
        return;
    }
    else if( val->IsNumber() )
    {
        unsigned char x = (unsigned char)val->Int32Value();
        this->append( &x, 1 );
        return;
    }
    else
    {
        JSByteArray * ba = cv::CastFromJS<JSByteArray>(val);
        if( !ba )
        {
            goto toss;
        }
        this->append( ba->rawBuffer(), ba->length() );
        return;
    }
    toss:
    v8::ThrowException(v8::Exception::Error(JSTR("Argument to append() must be one of (Number,String,ByteArray)")));
    return;
}

int JSByteArray::gzipTo( JSByteArray & dest, int level ) const
{
    return GZipJSByteArray( *this, dest, level );
}
int JSByteArray::gzipTo( JSByteArray & dest ) const
{
    return GZipJSByteArray( *this, dest, 3 );
}

int JSByteArray::gunzipTo( JSByteArray & dest ) const
{
    return GUnzipJSByteArray( *this, dest );
}

v8::Handle<v8::Value> JSByteArray::gzip() const
{
    v8::HandleScope sc;
    typedef cv::ClassCreator<JSByteArray> CW;
    v8::Handle<v8::Object> jba =
        CW::Instance().NewInstance( 0, NULL );
    JSByteArray * ba = cv::CastFromJS<JSByteArray>( jba );
    if( ! ba )
    {
        cv::StringBuffer msg;
        msg << "Creation of ByteArray object failed!";
        return v8::ThrowException( msg.toError() );
    }
    int const rc = this->gzipTo( *ba );
    if( rc )
    {
        CW::Instance().DestroyObject( jba );
        return v8::Null();
    }
    return sc.Close(jba);
}
v8::Handle<v8::Value> JSByteArray::gunzip() const
{
    v8::HandleScope sc;
    typedef cv::ClassCreator<JSByteArray> CW;
    v8::Handle<v8::Object> jba =
        CW::Instance().NewInstance( 0, NULL );
    JSByteArray * ba = cv::CastFromJS<JSByteArray>( jba );
    if( ! ba )
    {
        cv::StringBuffer msg;
        msg << "Creation of ByteArray object failed!";
        return v8::ThrowException( msg.toError() );
    }
    int const rc = this->gunzipTo( *ba );
    if( rc )
    {
        CW::Instance().DestroyObject( jba );
        return v8::Null();
    }
    return sc.Close(jba);
}


void JSByteArray::SetupBindings( v8::Handle<v8::Object> dest )
{
    using namespace v8;
    HandleScope scope;
    typedef JSByteArray N;
    typedef cv::ClassCreator<N> CW;
    CW & cw( CW::Instance() );
    //CERR <<"Binding class "<<TypeName<JSByteArray>::Value<<"...\n";
    if( cw.IsSealed() )
    {
        cw.AddClassTo( TypeName<JSByteArray>::Value, dest );
        return;
    }

    cw
        ( "destroy", CW::DestroyObjectCallback )
        ( "append", cv::MethodTo<InCa, N, void (v8::Handle<v8::Value> const &), &N::append>::Call )
        ( "stringValue", cv::MethodTo<InCa, const N, std::string (),&N::stringValue>::Call )
        ( "toString", cv::MethodTo<InCa, const N, std::string (),&N::toString>::Call )
        // i don't like these next two...
        //( "gzipTo", cv::ConstMethodToInCa<N, int (N &), &N::gzipTo>::Call )
        //( "gunzipTo", cv::ConstMethodToInCa<N, int (N &), &N::gunzipTo>::Call )
        ( "gzip", cv::MethodTo<InCa, const N, v8::Handle<v8::Value> (), &N::gzip>::Call )
        ( "gunzip", cv::MethodTo<InCa, const N, v8::Handle<v8::Value> (), &N::gunzip>::Call )
        ;
    v8::Handle<v8::ObjectTemplate> const & proto( cw.Prototype() );
    AccessorAdder acc(proto);
    acc( "length",
            MethodTo< Getter, const N,uint32_t(),&N::length>(),
            SetterCatcher_std< MethodTo< Setter, N, uint32_t (uint32_t), &N::length> >()
        )
        ( "isGzipped",
            MethodTo< Getter, const N, bool(),&N::isGzipped>(),
            ThrowingSetter()
        )
        ;
#if 0 // don't do this b/c the cost of the conversion (on each access) is deceptively high (O(N) time and memory, N=bytearray length)
    proto->SetAccessor( JSTR("stringValue"),
                        ConstMethodToGetter<N, std::string(),&N::stringValue>::Get,
                        ThrowingSetter::Set );
#endif
    v8::Handle<v8::FunctionTemplate> ctorTmpl = cw.CtorTemplate();
    ctorTmpl->InstanceTemplate()->SetIndexedPropertyHandler( JSByteArray::indexedPropertyGetter,
                                                             JSByteArray::indexedPropertySetter,
                                                             JSByteArray::indexedPropertyQuery,
                                                             NULL/*JSByteArray::indexedPropertyDeleter*/,
                                                             NULL/*JSByteArray::indexedPropertyEnumerator*/
                                                            );
    v8::Handle<v8::Function> ctor = cw.CtorFunction();

    ctor->Set(JSTR("enableDestructorDebug"), cv::CastToJS(cv::FunctionToInCa< void (bool), setEnableDestructorDebug>::Call) );
    cw.AddClassTo( TypeName<JSByteArray>::Value, dest );
    //CERR <<"Binding done.\n";
    return;
}

namespace cvv8 {

    int GZipJSByteArray( JSByteArray const & src, JSByteArray & dest, int level )
    {
#if ! ByteArray_CONFIG_ENABLE_ZLIB
        Toss("zlib functionality was not compiled in.");
        return -1;
#else
        /**
           Achtung: this impl was a quick hack port from another tree. It is
           not an optimal solution.
        */
        if( &src == &dest ) return -1;
        else if( level != Z_DEFAULT_COMPRESSION )
        {
            if( level < Z_NO_COMPRESSION ) level = Z_NO_COMPRESSION;
            else if (level > Z_BEST_COMPRESSION) level = Z_BEST_COMPRESSION;
        }
        {
            /* Code taken 99% from http://zlib.net/zlib_how.html */
            int ret;
            int flush;
            size_t have;
            z_stream strm;
            enum { bufSize  = 1024 * 8 };
            unsigned char const * in = NULL;
            unsigned char const * inPos = NULL;
            uint32_t const inLen = src.length();
            unsigned char out[bufSize];
            memset( &strm, 0, sizeof(z_stream) );

            in = (unsigned char const *)src.rawBuffer();
            inPos = in;
            /* allocate deflate state */
            strm.zalloc = Z_NULL;
            strm.zfree = Z_NULL;
            strm.opaque = Z_NULL;
            ret = /*deflateInit(&strm, level) */
                deflateInit2( &strm, level, Z_DEFLATED, 16+MAX_WBITS /*gzip compat*/, 8, Z_DEFAULT_STRATEGY )
                ;
            if (ret != Z_OK)
            {
                return ret;
            }

            /* compress until end of file */
            do
            {
                size_t iosize = bufSize;
                if( (inPos + iosize) >= (in + inLen) )
                {
                    iosize = in + inLen - inPos;
                }
                strm.avail_in = iosize;
                flush = (iosize < bufSize) ? Z_FINISH : Z_NO_FLUSH;
                strm.next_in = (Bytef *)inPos;
                inPos += iosize;
                /* run deflate() on input until output buffer not full, finish
                   compression if all of source has been read in */
                do
                {
                    strm.avail_out = bufSize;
                    strm.next_out = out;
                    ret = deflate(&strm, flush);    /* no bad return value */
                    if( Z_STREAM_ERROR == ret )
                    {
                        (void)deflateEnd(&strm);
                        return Z_STREAM_ERROR;
                    }
                    have = bufSize - strm.avail_out;
                    if( have )
                    {
                        dest.append( out, have );
                    }
                } while (strm.avail_out == 0);
                if( strm.avail_in != 0)
                {
                    fprintf(stderr,"Not all input was consumed! %u byte(s) remain!",
                            (unsigned int) strm.avail_in );
                    (void)deflateEnd(&strm);
                    return Z_STREAM_ERROR;
                }
                /* done when last data in file processed */
            } while (flush != Z_FINISH);
            /*assert(ret == Z_STREAM_END);        //stream will be complete */
            /* clean up and return */
            (void)deflateEnd(&strm);
            return (ret == Z_STREAM_END) ? Z_OK : ret;
        }
#endif /* ByteArray_CONFIG_ENABLE_ZLIB */
    }

    int GUnzipJSByteArray( JSByteArray const & src, JSByteArray & dest )
    {
#if ! ByteArray_CONFIG_ENABLE_ZLIB
        Toss("zlib functionality was not compiled in.");
        return -1;
#else
        /**
           Achtung: this impl was a quick hack port from another tree. It is
           not an optimal solution.
        */
        if( &src == &dest ) return -1;
        else
        {
            /* Code taken 99% from http://zlib.net/zlib_how.html */
            int ret;
            size_t have;
            z_stream strm;
            enum { bufSize  = 1024 * 8 };
            unsigned char const * in = (unsigned char const *)src.rawBuffer();
            unsigned char const * inPos = in;
            uint32_t const inLen = src.length();
            unsigned char out[bufSize];
            memset( &strm, 0, sizeof(z_stream) );
            strm.zalloc = Z_NULL;
            strm.zfree = Z_NULL;
            strm.opaque = Z_NULL;
            strm.avail_in = 0;
            strm.next_in = Z_NULL;
            ret = /*inflateInit( &strm ) */
                inflateInit2( &strm, 16+MAX_WBITS /* for gzip compatibility */ )
                /* valgrind says:

                ==4503== Conditional jump or move depends on uninitialised value(s)
                ==4503==    at 0x5B8EE40: inflateReset2 (in /lib/libz.so.1.2.3.4)
                ==4503==    by 0x5B8EF2F: inflateInit2_ (in /lib/libz.so.1.2.3.4)
                ==4503==    by 0x4E3E91C: whio_stream_gunzip (whio_zlib.c:130)
                ...
                ==4503==  Uninitialised value was created by a heap allocation
                ==4503==    at 0x4C2815C: malloc (vg_replace_malloc.c:236)
                ==4503==    by 0x5B8EF0B: inflateInit2_ (in /lib/libz.so.1.2.3.4)
                ==4503==    by 0x4E3E91C: whio_stream_gunzip (whio_zlib.c:130)
                ...

                but i have no clue why.

                (is libz really version 1.2.3.4?)
                */
                ;
            if (ret != Z_OK)
            {
                return ret;
            }
            do
            {
                size_t iosize = bufSize;
                if( (inPos + iosize) >= (in + inLen) )
                {
                    iosize = in + inLen - inPos;
                }
                strm.avail_in = iosize;
                if (strm.avail_in == 0)
                    break;
                strm.next_in = (Bytef *)inPos;
                inPos += iosize;
                /* run inflate() on input until output buffer not full */
                do
                {
                    strm.avail_out = bufSize;
                    strm.next_out = out;
                    ret = inflate(&strm, Z_NO_FLUSH);
                    switch (ret)
                    {
                      case Z_NEED_DICT:
                          ret = Z_DATA_ERROR; /* and fall through */
                      case Z_STREAM_ERROR:
                      case Z_DATA_ERROR:
                      case Z_MEM_ERROR:
                          (void)inflateEnd(&strm);
                          return ret;
                      default:
                          break;
                    }
                    have = bufSize - strm.avail_out;
                    if( have )
                    {
                        dest.append( out, have );
                    }
                } while (strm.avail_out == 0);
                /* done when inflate() says it's done */
            } while (ret != Z_STREAM_END);
            (void)inflateEnd( &strm );
            return (ret == Z_STREAM_END) ? Z_OK : Z_DATA_ERROR;
        }
#endif /* ByteArray_CONFIG_ENABLE_ZLIB */
    }

}// namespace
#undef DBGOUT
#undef JSTR
#undef BA_JS_CLASS_NAME
#undef CERR
#undef ByteArray_CONFIG_ENABLE_ZLIB
