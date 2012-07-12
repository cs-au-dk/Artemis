/************************************************************************
This file contains v8 bindings for the cpdo db abstraction layer
(http://fossil.wanderinghorse.net/repos/cpdo/). We call it JSPDO.

This file gives a fairly complete demonstration of what cvv8's
class/function/method-binding mechanisms can do. In particular, it 
demonstrates that we can bind 3rd-party C++ classes (in this case 
from cpdo) which were not designed specifically for v8, and can 
often do so without subclassing or modifying those classes.

License: this code is released into the Public Domain by its author,
Stephan Beal (http://wanderinghorse.net/home/stephan/). HOWEVER, if
you enable the MySQL driver (by compiling with
-DCPDO_ENABLE_MYSQL5=ATrueValue) then you must inherit the GPL license
used by MySQL (if any). Linking against sqlite3 does not impose any
specific licensing restrictions on the client (not even a "do no evil"
clause).
************************************************************************/
#if defined(NDEBUG)
#  undef NDEBUG
#endif

#include <cassert>
#include "cpdo_amalgamation.hpp"

#include "cvv8/ClassCreator.hpp"
#include "cvv8/properties.hpp"

#include "jspdo.hpp"
#include "bytearray.hpp"

#include <iostream>
#include <fstream>
#include <iterator>
#include <algorithm>
#include <map>
#include <sstream>

#ifndef CERR
#define CERR std::cerr << __FILE__ << ":" << std::dec << __LINE__ << ":" <<__FUNCTION__ << "(): "
#endif

#define JSTR(X) v8::String::New(X)

#define JSPDO_CLASS_NAME "JSPDO" /* JSPDO class name, as it should appear in JS. */

namespace {
    bool enableDestructorDebug = false;
    
    void setEnableDestructorDebug( bool b )
    {
        enableDestructorDebug = b;
    }
}
namespace cv = cvv8;
namespace jspdo {

#if 0
    /**
        Not yet used, but something to consider so that we can finalize any
        statements left open when the db closes. Adding this requires some other
        refactoring.
    */
    class JSPDO : public cpdo::driver {
        public:
            typedef std::map< void const *, v8::Handle<v8::Object> > StmtMap;
            StmtMap stmts;
            //cpdo::driver * drv;
            JSPDO( char const * dsn, char const * user, char const * pw )
                : cpdo::driver(dsn,user,pw),
                  stmts()
            {}
            //~ JSPDO() : stmts()//,drv(NULL)
            //~ {
            //~ }
            virtual ~JSPDO()/*defined out-of-line for templating reasons!*/;
    };
#endif
}

namespace cvv8 {
    CVV8_TypeName_DECL((cpdo::driver));
    CVV8_TypeName_DECL((cpdo::statement));
    CVV8_TypeName_IMPL((cpdo::driver),"JSPDO");
    CVV8_TypeName_IMPL((cpdo::statement),"Statement");

    // Various ClassCreator policy classes specialized for the native types
    // we are binding...

#if 1
    /** We don't really need the extra type-safety bits for Statement b/c
        subclassing will never be an issue (b/c client code can't create
        Statements directly (or it's not in the public API, anyway)).
    */
    template <>
    struct ClassCreator_InternalFields<cpdo::statement>
        : ClassCreator_InternalFields_Base<cpdo::statement,3,0,1>
    {};
#endif
    template <>
    struct ClassCreator_SearchPrototypeForThis<cpdo::statement> : Opt_Bool<false>
    {};

    template <>
    class ClassCreator_Factory<cpdo::driver>
    {
    public:
        typedef cpdo::driver * ReturnType;
        static ReturnType Create( v8::Persistent<v8::Object> jsSelf, v8::Arguments const & argv );
        static void Delete( cpdo::driver * obj );
    };

    template <>
    class ClassCreator_Factory<cpdo::statement>
    {
    public:
        typedef cpdo::statement * ReturnType;
        static ReturnType Create( v8::Persistent<v8::Object> jsSelf, v8::Arguments const & argv );
        static void Delete( cpdo::statement * obj );
    };
    
    template <>
    struct JSToNative<cpdo::driver>
        : JSToNative_ClassCreator<cpdo::driver>
    {};

    template <>
    struct JSToNative<cpdo::statement>
        : JSToNative_ClassCreator<cpdo::statement>
    {};

    /** Enum-to-int conversion workaround. */
    template <>
    struct NativeToJS<cpdo_data_type> : NativeToJS<int32_t> {};

}
namespace jspdo {
#if 0
    JSPDO::~JSPDO()
    {
        if( enableDestructorDebug )
        {
            CERR << "Destructing native JSPDO@"<<(void const *)this<<'\n';
        }
        if( ! this->stmts.empty() ) {
            typedef cv::ClassCreator<cpdo::statement> CC;
            StmtMap map;
            map.swap( this->stmts );
            StmtMap::iterator it( map.begin() );
            for( ; map.end() != it; ++it ) {
                CC::DestroyObject((*it).second);
            }
        }
        //delete this->drv;
    }
#endif

    /* The following plumbing is to map Statments to their owning
       DBs. We do this to cover up for sloppy script code which does not
       close statements before the db is closed (leading to undefined
       behaviour). So we manage the relationships and try to DTRT.
    */

    /**
        Map of cpdo::statement to their JS selves.
    */
    typedef std::map< void const *, v8::Handle<v8::Object> > StmtMap;
    /**
        Map of cpdo::driver to StmtMap.
    */
    typedef std::map< void const *, StmtMap > DbMap;


    /**
        Shared DbMap instance. This is used so we can add plumbing to
        "safely" close statement handles at db close()-time if the 
        client failed to do so earlier (in strict violation of the 
        documentation, i might add!). Though this whole mess is 
        unsightly, it's less unsightly than seeing a script crash 
        one's app due to stepping on an invalidated native pointer 
        during garbage collection.
        
        Reminder about locking: v8 only runs in one thread at a time
        and will only switch threads under specific conditions (e.g.
        at certain function boundaries), none of which
        we meet while using this data. i.e. we are piggybacking on
        v8's locking semantics here.
    */
    struct DbMapLocker
    {
#if 0 // we probably don't need this, since this class is only used from inside called-from-v8 code.
    private:
        v8::Locker lock;
    public:
        DbMapLocker() : lock()
        {
        }
#else
        DbMapLocker()
        {
        }
#endif
        DbMap & map()
        {
            static DbMap bob;
            return bob;
        }
        
    };

    /**
        Returns true if JSPDO.enableDebug == true. Must not be called
        before JSPDO::SetupBindings() has been called, nor after
        v8 cleans up/shuts down.
    */
    static bool IsDebugEnabled();
}

namespace cvv8 {

    typedef ClassCreator_InternalFields<cpdo::statement> CCI_Stmt;
    const static char AssertStatementInternalFieldSanityCheck[ (CCI_Stmt::Count>2) ? 1 : -1 ] = {0};
    enum {
        //! The v8::Object internal field number to store the Driver-for-Statement mapping.
        StatementDrvInternalField = CCI_Stmt::Count-1
    };

    /**
        This specialization adds some plumbing to allow the framework
        to gracefully clean up any Statement objects which clients fail
        to close.
    */
    template <>
    struct ClassCreator_WeakWrap<cpdo::statement>
    {
    private:
        static cpdo::driver const * getDriverForStmt( void const * self, v8::Handle<v8::Object> const & jsSelf )
        {
            typedef ClassCreator_InternalFields<cpdo::statement> CCI;
            v8::Handle<v8::Value> const & db( jsSelf->GetInternalField(StatementDrvInternalField) );
            cpdo::driver const * drv = cv::CastFromJS<cpdo::driver>( db );
#if 0
            if( !drv )
            { // this happens during db.close() cleanup of "dangling" statements.
                CERR << "Driver is NULL for cpdo::statement@"<<self<<'\n';
                assert( 0 && "Driver is NULL!" );
            }
#endif
            return drv;
        }
    public:
        typedef cpdo::statement * NativeHandle;
        static void PreWrap( v8::Persistent<v8::Object> const & jsSelf, v8::Arguments const & argv )
        {
            return;
        }
        static void Wrap( v8::Persistent<v8::Object> const & jsSelf, NativeHandle nativeSelf )
        {
            cpdo::driver const * drv = getDriverForStmt(nativeSelf,jsSelf);
            if( drv )
            {
                v8::Locker const lock;
                jspdo::DbMapLocker().map()[drv][nativeSelf] = jsSelf;
            }
            return;
        }
        static void Unwrap( v8::Handle<v8::Object> const & jsSelf, NativeHandle nativeSelf )
        {
            if( ! nativeSelf ) return /* happens in some (invalid) combinations of cleanup. */;
            cpdo::driver const * drv = getDriverForStmt(nativeSelf,jsSelf);
            if( drv )
            {
                jspdo::DbMapLocker().map()[drv].erase(nativeSelf);
            }
            return;
        }
    };

    
    cpdo::statement * ClassCreator_Factory<cpdo::statement>::Create( v8::Persistent<v8::Object> jsSelf,
                                                                     v8::Arguments const & argv )
    {
        if( argv.Length() < 2 )
        {
            throw std::range_error("The JSPDO constructor requires 1-3 arguments.");
        }
        v8::Handle<v8::Value> const & jdrv(argv[0]);
        cpdo::driver * drv = cv::CastFromJS<cpdo::driver>(jdrv);
        if( ! drv )
        {
            throw std::range_error("The Statement ctor must not be called directly from client code.");
        }
        v8::Handle<v8::String> const & sql(argv[1]->ToString());
        v8::String::Utf8Value const u8v(sql);
        cpdo::statement * rc = drv->prepare( *u8v );
        typedef ClassCreator_InternalFields<cpdo::statement> CCI;
        jsSelf->SetInternalField(StatementDrvInternalField,jdrv);
        jsSelf->Set(JSTR("sql"),sql);
        if( jspdo::IsDebugEnabled() )
        {
            CERR << "Created cpdo::statement@"<<(void const *)rc<<'\n';
        }
        return rc;
    }

    void ClassCreator_Factory<cpdo::statement>::Delete( cpdo::statement * st )
    {
        if( jspdo::IsDebugEnabled() || enableDestructorDebug )
        {
            CERR << "Destroying cpdo::statement@"<<(void const *)st<<'\n';
        }

        jspdo::DbMapLocker ml;
        jspdo::DbMap & map(ml.map());
        jspdo::DbMap::iterator it = map.begin();
        for( ; map.end() != it; ++it )
        {
            jspdo::StmtMap::iterator sit = (*it).second.find(st);
            if( (*it).second.end() == sit ) continue;
            (*it).second.erase(st);
            break;
        }
        delete st;
    }

    cpdo::driver * ClassCreator_Factory<cpdo::driver>::Create( v8::Persistent<v8::Object> jsSelf,
                                                               v8::Arguments const & argv )
    {
        if( argv.Length() < 1 )
        {
            throw std::range_error("The JSPDO constructor requires 1-3 arguments.");
        }
        std::string dsn = cv::CastFromJS<std::string>(argv[0]);
        std::string user = (argv.Length()>1) ? cv::CastFromJS<std::string>(argv[1]) : std::string();
        std::string pass = (argv.Length()>2) ? cv::CastFromJS<std::string>(argv[2]) : std::string();
        cpdo::driver * db = new cpdo::driver( dsn.c_str(), user.c_str(), pass.c_str() );
        jsSelf->Set(JSTR("dsn"), argv[0]);
        if( jspdo::IsDebugEnabled() )
        {
            CERR << "Created cpdo::driver@"<<(void const *)db<<'\n';
        }
        return db;
    }

    void ClassCreator_Factory<cpdo::driver>::Delete( cpdo::driver * drv )
    {
        if( jspdo::IsDebugEnabled() || enableDestructorDebug )
        {
            CERR << "Destroying cpdo::driver@"<<(void const *)drv<<'\n';
        }
        /**
            The following code (everything but the (delete drv)) is only
            here to try to clean up statements which the client failed
            to clean up. We must do this or risk a crash (or other
            Undefined Behaviour) if the statement is later
            garbage-collected.
        */
        jspdo::DbMapLocker mo;
        jspdo::DbMap & map(mo.map());
        jspdo::DbMap::iterator it = map.find(drv);
        if( map.end() != it )
        {
            typedef cv::ClassCreator<cpdo::statement> CCS;
            jspdo::StmtMap smap;
            {
                jspdo::StmtMap & smapX((*it).second);
                smap.swap(smapX);
                map.erase(drv);
            }
            jspdo::StmtMap::iterator sit(smap.begin());
            for( ; smap.end() != sit; ++sit )
            {
                if( jspdo::IsDebugEnabled() || enableDestructorDebug )
                {
                    CERR << "JSPDO.close() is cleaning up a dangling/unclosed cpdo::statement@"<<(*sit).first<<'\n';
                }
                CCS::Instance().DestroyObject( (*sit).second );
            }
        }
        
        delete drv;
    }
}

namespace jspdo {
    bool IsDebugEnabled()
    {
        typedef cv::ClassCreator<cpdo::driver> CC;
        CC & cc( CC::Instance() );
        v8::Handle<v8::Value> const & x( cc.CtorFunction()->Get(JSTR("enableDebug")) );
        return x.IsEmpty() ? false : x->BooleanValue();
    }
}

// Internal convenience macros...
#define STMT_DECL(JVAL) cpdo::statement * st = cv::CastFromJS<cpdo::statement>(JVAL)
#define ASSERT_STMT_DECL(JVAL) STMT_DECL(JVAL); \
    if( ! st ) return v8::ThrowException(v8::Exception::Error(JSTR("Could not find native cpdo::statement 'this' object.")))
#define DRV_DECL(JVAL) cpdo::driver * drv = cv::CastFromJS<cpdo::driver>(JVAL)
#define ASSERT_DRV_DECL(JVAL) DRV_DECL(JVAL); \
    if( ! drv ) return v8::ThrowException(v8::Exception::Error(JSTR("Could not find native cpdo::driver 'this' object.")))
#define ASSERT_ARGV(COND) if( ! (COND) ) return v8::ThrowException(v8::Exception::Error(JSTR("Arguments condition failed: "#COND)))

//! JSPDO.toString() impl
v8::Handle<v8::Value> JSPDO_toString( v8::Arguments const & argv )
{
    DRV_DECL(argv.This());
    cv::StringBuffer buf;
    buf << "[cpdo::driver@"<<(void const *)drv;
    if( drv )
    {
        buf << ", driver="<<drv->driver_name();
    }
    return buf << ']';
}

//! JSPDO.Statement.toString() impl
v8::Handle<v8::Value> Statement_toString( v8::Arguments const & argv )
{
    STMT_DECL(argv.This());
    cv::StringBuffer sb;
    sb << "[cpdo::statement@"<<(void const *)st;
    if( st )
    {
        v8::Handle<v8::Value> const v(argv.This()->Get(JSTR("sql")));
        if( !v.IsEmpty() && v->IsString()) sb << ", sql=["<<v<<"]";
    }
    return sb << ']';
}

//! JSPDO.Statement.get() impl for Number values.
v8::Handle<v8::Value> Statement_getNumber(cpdo::statement * st,
                                          uint16_t ndx )
{
    const cpdo_data_type colType = st->col_type(ndx);
    switch( colType )
    {
      case CPDO_TYPE_INT8:
          return v8::Integer::New( st->get_int8(ndx) );
      case CPDO_TYPE_INT16:
          return v8::Integer::New( st->get_int16(ndx) );
      case CPDO_TYPE_INT32:
          return v8::Integer::New( st->get_int32(ndx) );
      case CPDO_TYPE_INT64:
          /* This is somewhat evil. v8 doesn't support 64-bit integers, so we'll
             upgrade them to doubles.
          */
          return v8::Number::New( static_cast<double>(st->get_int64(ndx)) );
      case CPDO_TYPE_FLOAT:
          return v8::Number::New( st->get_float(ndx) );
      case CPDO_TYPE_DOUBLE:
          return v8::Number::New( st->get_double(ndx) );
      default: {
          cv::StringBuffer msg;
          msg << "Internal error ("<<__FILE__<<":"<<__LINE__
              <<"): unhandled db field type (CPDO_TYPE code "
              <<(int)colType<<") found for result column "<<ndx<<'.';
          return v8::ThrowException(msg.toError());
      }
    }
}

//! JSPDO.Statement.get() impl for String/Blob values.
static v8::Handle<v8::Value> Statement_getString(cpdo::statement * st,
                                                 uint16_t ndx )
{
    cpdo_data_type const colType = st->col_type(ndx);
    switch( colType )
    {
      case CPDO_TYPE_NULL:
          return v8::Null();
      case CPDO_TYPE_INT8:
          return cv::StringBuffer() << (int)st->get_int8(ndx);
      case CPDO_TYPE_INT16:
          return cv::StringBuffer() << st->get_int16(ndx);
      case CPDO_TYPE_INT32:
          return cv::StringBuffer() << st->get_int32(ndx);
      case CPDO_TYPE_INT64:
          /*This is arguably evil b/c v8 doesn't support 64-bit integers.*/
          return cv::StringBuffer() << st->get_int64(ndx);
      case CPDO_TYPE_FLOAT:
          return cv::StringBuffer() << st->get_float(ndx);
      case CPDO_TYPE_DOUBLE:
          return cv::StringBuffer() << st->get_double(ndx);
      case CPDO_TYPE_STRING: {
          char const * str = NULL;
          uint32_t len = 0;
          str = st->get_string(ndx,&len);
          if( str && len ) return v8::String::New(str,len);
          else return v8::Null();
      }
      default: {
          // reminder to self: why might need to treat CPDO_TYPE_CUSTOM as string for the
          // sake of MySQL DATE/TIME-related fields.
          cv::StringBuffer msg;
          msg << "Internal error("<<__FILE__<<":"<<__LINE__
              <<"): unhandled db field type (CPDO_TYPE code "
              <<(int)colType<<") found for result column "<<ndx<<'.';
          return v8::ThrowException(msg.toError());
      }
    }
}

//! Main JSPDO.Statement.get() impl.
static v8::Handle<v8::Value> Statement_get( cpdo::statement * st,
                                            uint16_t ndx )
{
    cpdo_data_type const colType = st->col_type(ndx);
    switch( colType )
    {
      case CPDO_TYPE_NULL:
          return v8::Null();
      case CPDO_TYPE_INT8:
      case CPDO_TYPE_INT16:
      case CPDO_TYPE_INT32:
      case CPDO_TYPE_INT64:
      case CPDO_TYPE_FLOAT:
      case CPDO_TYPE_DOUBLE:
          return Statement_getNumber(st, ndx);
      case CPDO_TYPE_STRING:
          return Statement_getString(st, ndx);
      case CPDO_TYPE_BLOB: {
          void const * blob = NULL;
          uint32_t slen = 0;
          blob = st->get_blob(ndx, &slen);
          if( !blob || !slen ) return v8::Null();
          typedef cv::ClassCreator<cv::JSByteArray> BAC;
          v8::Handle<v8::Object> baObj( BAC::Instance().NewInstance( 0, NULL ) );
          if( baObj.IsEmpty() ) return v8::Undefined() /* assume exception is propagating. */;
          cv::JSByteArray * ba = cv::CastFromJS<cv::JSByteArray>(baObj);
          if( ! ba ) return cv::Toss("Allocation of ByteArray failed.");
          ba->append( blob, slen );
          return baObj;
      }
      default: {
          // reminder to self: why might need to treat CPDO_TYPE_CUSTOM as string or blob for the
          // sake of MySQL DATE/TIME-related fields.
          cv::StringBuffer msg;
          msg << "Internal error: unhandled db field type (CPDO_TYPE code "
              <<(int)colType<<") found for result column "<<ndx<<'.';
          return v8::ThrowException(msg.toError());
      }
    }
}

//! Main JSPDO.Statement.get() impl.
v8::Handle<v8::Value> Statement_get(v8::Arguments const & argv)
{
    ASSERT_ARGV(argv.Length()>0);
    ASSERT_STMT_DECL(argv.This());
    return Statement_get( st, cv::CastFromJS<uint16_t>(argv[0]) );
}

//! JSPDO.Statement.bind(int[,val]) impl.
static v8::Handle<v8::Value> Statement_bind(cpdo::statement * st,
                                            uint16_t ndx,
                                            v8::Handle<v8::Value> const & val )
{
    assert( st && !val.IsEmpty() );
    if( val->IsNull() || val->IsUndefined() )
    {
        st->bind( ndx );
    }
    else if( val->IsNumber() )
    {
        if( val->IsInt32() )
        {
            st->bind( ndx, val->Int32Value() );
        }
        else if( val->IsUint32() )
        {
            st->bind( ndx, static_cast<int64_t>(val->Uint32Value()) );
        }
        else
        {
            st->bind( ndx, val->NumberValue() );
        }
    }
    else if( val->IsObject() )
    {
        cv::JSByteArray const * other = cv::CastFromJS<cv::JSByteArray>(val);
        if( ! other )
        {
            return v8::ThrowException(v8::Exception::Error(JSTR("bind(Object) was passed a non-ByteArray object.")));
        }
        if( other->length() )
        {
            st->bind( ndx, other->rawBuffer(), other->length() );
        }
        else
        {
            st->bind( ndx );
        }
    }
    else if( val->IsString() )
    {
        v8::String::Utf8Value const ustr(val);
        char const * cstr = *ustr;
        if( !cstr )
        {
            st->bind(ndx);
        }
        else
        {/**
            TODO: try to bind as a blob and if that fails then bind as
            a string (or the other way around). To do that without
            adding a try/catch block we have to use the low-level cpdo
            API.
          */
            st->bind( ndx, cstr, static_cast<uint32_t>(ustr.length()) );
        }
    }
    else if( val->IsBoolean() )
    {
        st->bind( ndx, static_cast<int8_t>(val->BooleanValue() ? 1 : 0) );
    }
    else
    {
        return v8::ThrowException((cv::StringBuffer()
                                  << "bind() was given an invalid parameter "
                                  << "type for column "<<ndx<<".").toError());
    }
    return v8::Undefined();
}

//! JSPDO.Statement.bind(string[,val]) impl.
static v8::Handle<v8::Value> Statement_bind(cpdo::statement * st,
                                            std::string const & pname,
                                            v8::Handle<v8::Value> const & val )
{
    char const * cstr = pname.empty() ? NULL : pname.c_str();
    return Statement_bind( st, st->param_index( cstr ), val );
}

//! JSPDO.Statement.bind(string|int[,val]) impl.
static v8::Handle<v8::Value> Statement_bind(cpdo::statement * st,
                                            v8::Handle<v8::Value> const & index,
                                            v8::Handle<v8::Value> const & val )
{
    return index->IsString()
        ? Statement_bind( st, cv::JSToStdString(index), val )
        : Statement_bind( st, cv::CastFromJS<uint16_t>(index), val )
        ;
}

//! JSPDO.Statement.bind(Array) impl.
static v8::Handle<v8::Value> Statement_bind(cpdo::statement * st,
                                            v8::Handle<v8::Array> & ar )
{
    uint32_t const alen = ar->Length();
    uint16_t ndx = 1;
    for( ; ndx <= alen; ++ndx )
    {
        v8::Handle<v8::Value> const & rc( Statement_bind( st, ndx, ar->Get( ndx - 1 ) ) );
        if( rc.IsEmpty() )
        {
            // JS exception was thrown.
            return rc;
        }
    }
    return v8::Undefined();
}

//! JSPDO.Statement.bind(Object) impl.
static v8::Handle<v8::Value> Statement_bind(cpdo::statement * st,
                                            v8::Handle<v8::Object> & obj )
{
    v8::Local<v8::Array> plist( obj->GetPropertyNames() );
    v8::Handle<v8::Value> rc;
    uint32_t const alen = plist->Length();
    uint32_t i = 0;
    for( ; i < alen; ++i )
    {
        v8::Local<v8::Value> const key = plist->Get( i );
        if( key.IsEmpty() ) continue;
        v8::Local<v8::String> skey( v8::String::Cast(*key) );
        if( ! obj->HasOwnProperty(skey) || (skey->Length()<1) ) continue;
        else if( ':' != *(*v8::String::AsciiValue(skey)) )
        {
            std::string const & colon( ":"+cv::JSToStdString(skey) );
            skey = v8::String::New(colon.c_str(), static_cast<int>(colon.size()) );
        }
        rc = Statement_bind( st, skey, obj->Get(key/*NOT skey! We might have changed it!*/) );
        if( rc.IsEmpty() )
        { // JS exception
            return rc;
        }
    }
    return v8::Undefined();
}


/**
   ! Main JSPDO.Statement.bind() impl.
*/
v8::Handle<v8::Value> Statement_bind(v8::Arguments const & argv)
{
    ASSERT_STMT_DECL(argv.This());
    v8::Handle<v8::Value> val;
    int const argc = argv.Length();
    if( !argc || (argc > 2) )
    {
        return v8::ThrowException(JSTR("bind() requires 1 or 2 arguments."));
    }
    if( 2 == argc )
    {
        return Statement_bind( st, argv[0], argv[1] );
    }
    else /* one argument */
    {
        val = argv[0];
        if( val->IsArray() )
        {
            v8::Handle<v8::Array> ar((v8::Array::Cast(*val)));
            return Statement_bind( st, ar );
        }
        else if( val->IsObject() )
        {
            v8::Handle<v8::Object> obj((v8::Object::Cast(*val)));
            return Statement_bind( st, obj );
        }
        else
        {
            return Statement_bind( st, val, v8::Null() );
        }
    }
}

//! JSPDO.Statement.stepArray() impl.
v8::Handle<v8::Value> Statement_stepArray( v8::Arguments const & argv )
{
    v8::HandleScope hscope;
    ASSERT_STMT_DECL(argv.This());
    if( ! st->step() ) return v8::Null();
    uint16_t const colCount = st->col_count();
    if( ! colCount ) return v8::Null() /* fixme: throw here. */;
    v8::Handle<v8::Array> arh( v8::Array::New(colCount) );
    uint16_t i = 0;
    for( ; i < colCount; ++i )
    {
        arh->Set( i, Statement_get(st, i) );
    }
    return hscope.Close(arh);
}

//! JSPDO.Statement.stepObject() impl.
v8::Handle<v8::Value> Statement_stepObject( v8::Arguments const & argv )
{
    v8::HandleScope hscope;
    ASSERT_STMT_DECL(argv.This());
    if( ! st->step() ) return v8::Null();
    uint16_t const colCount = st->col_count();
    if( ! colCount ) return v8::Null() /* fixme: throw here. */;
    char const * colName = NULL;
    v8::Handle<v8::Object> obj( v8::Object::New() );
    uint16_t i = 0;
    for( ; i < colCount; ++i )
    {
        colName = st->col_name(i);
        if( ! colName ) continue;
        obj->Set( JSTR(colName), Statement_get(st, i) );
    }
    return hscope.Close(obj);
}

/**
   Statement.columnNames accessor which caches the column names in
   an internal JS array.
*/
static v8::Handle<v8::Value> Statement_getColumnNames( v8::Local< v8::String > property,
                                                       const v8::AccessorInfo & info )
{
    try
    {
        ASSERT_STMT_DECL(info.This());
        v8::Handle<v8::Object> self( info.This() );
        char const * prop = "columnNames";
        v8::Handle<v8::String> jProp(JSTR(prop));
        v8::Handle<v8::Value> val( self->GetHiddenValue(jProp) );
        if( val.IsEmpty() )
        {
            uint16_t colCount = st->col_count();
            if( ! colCount )
            {
                val = v8::Null();
            }
            else
            {
                v8::Handle<v8::Array> ar( v8::Array::New(colCount) );
                for( uint16_t i = 0; i < colCount; ++i )
                {
                    char const * n = st->col_name(i);
                    if( ! n ) continue;
                    ar->Set( i, JSTR(n) );
                }
                val = ar;
            }
            self->SetHiddenValue(jProp, val);
        }
        return val;
    }
    catch(std::exception const & ex)
    {
        return cv::Toss(cv::CastToJS(ex));
    }
    catch(...)
    {
        return cv::Toss("columnNames accessor threw an unknown native exception!");
    }
        
}

#if 0
/**
   Statement.columnTypes accessor which caches the column types in
   an internal JS array.
   
   This has unfortunate semantic differences from columnType(), so
   it has been disabled.
*/
static v8::Handle<v8::Value> Statement_getColumnTypes( v8::Local< v8::String > property,
                                                       const v8::AccessorInfo & info )
{
    try
    {
        ASSERT_STMT_DECL(info.This());
        v8::Handle<v8::Object> self( info.This() );
        char const * prop = "columnTypes";
        v8::Handle<v8::String> jProp(JSTR(prop));
        v8::Handle<v8::Value> val( self->GetHiddenValue(jProp) );
        if( val.IsEmpty() )
        {
            uint16_t colCount = st->col_count();
            if( ! colCount )
            {
                val = v8::Null();
            }
            else
            {
                v8::Handle<v8::Array> ar( v8::Array::New(colCount) );
                for( uint16_t i = 0; i < colCount; ++i )
                {
                    cpdo_data_type const t = st->col_type(i);
                    ar->Set( i, v8::Integer::New(t) );
                }
                val = ar;
            }
            self->SetHiddenValue(jProp, val);
        }
        return val;
    }
    catch(std::exception const & ex)
    {
        return cv::Toss(cv::CastToJS(ex));
    }
    catch(...)
    {
        return cv::Toss("columnTypes accessor threw an unknown native exception!");
    }
        
}
#endif


/**
   Statement.paramNames accessor which caches the column names in
   an internal JS object.
*/
static v8::Handle<v8::Value> Statement_getParamNames( v8::Local< v8::String > property,
                                                       const v8::AccessorInfo & info )
{
    try
    {
        ASSERT_STMT_DECL(info.This());
        v8::Handle<v8::Object> self( info.This() );
        char const * prop = "columnNames";
        v8::Handle<v8::String> jProp(JSTR(prop));
        v8::Handle<v8::Value> val( self->GetHiddenValue(jProp) );
        if( val.IsEmpty() )
        {
            uint16_t colCount = st->param_count();
            if( ! colCount )
            {
                val = v8::Null();
            }
            else
            {
                v8::Handle<v8::Array> ar( v8::Array::New(colCount) );
                for( uint16_t i = 1/*bind ndx starts at 1*/; i <= colCount; ++i )
                {
                    char const * n = st->param_name(i);
                    if( ! n ) continue;
                    ar->Set( i-1, JSTR(n) );
                }
                val = ar;
            }
            self->SetHiddenValue(jProp, val);
        }
        return val;
    }
    catch(std::exception const & ex)
    {
        return cv::Toss(cv::CastToJS(ex));
    }
    catch(...)
    {
        return cv::Toss("paramNames accessor threw an unknown native exception!");
    }
        
}


//! JSPDO.prepare() impl.
v8::Handle<v8::Value> JSPDO_prepare( v8::Arguments const & argv )
{
    if( argv.Length() < 1 )
    {
        throw std::range_error("prepare() requires 1 argument (the SQL to prepare).");
    }
    ASSERT_DRV_DECL(argv.This());
    try
    {
        v8::HandleScope hscope;
        typedef cv::ClassCreator<cpdo::statement> WST;
        WST & wst( WST::Instance() );
        v8::Handle<v8::Value> stArgs[] = {
        argv.This(),
        argv[0]
        };
        v8::Handle<v8::Value> jSt = wst.NewInstance( 2, stArgs );
        if( jSt.IsEmpty() || ! jSt->IsObject() ) {
            /* i'm assuming this is an exception for now */
            return jSt;
        }
        cpdo::statement * st = cv::CastFromJS<cpdo::statement>(jSt);
        assert( (NULL != st) && "Probable bug in the binding code." );
        return hscope.Close(jSt);
    }
    catch(std::exception const &ex)
    {
        return cv::Toss(cv::CastToJS(ex));
    }
}

//! JSPDO.exec() impl.
v8::Handle<v8::Value> JSPDO_exec( v8::Arguments const & argv )
{
    if( argv.Length() < 1 ) {
        throw std::range_error("exec() requires 1 argument.");
    }
    ASSERT_DRV_DECL(argv.This());
    v8::Handle<v8::Value> const val(argv[0]);
    if( val->IsString() ) {
        std::string sql = cv::JSToStdString(argv[0]);
        drv->exec( sql.c_str(), sql.size() );
        return v8::Undefined();
    }
    else if( val->IsObject() ) {
        v8::Handle<v8::Value> ac[] = {val};
        return v8::Function::Cast( *(argv.This()->Get(JSTR("execForeach"))) )
            ->Call( argv.This(), 1, ac );
    }
    else {
        return v8::ThrowException(v8::Exception::Error(JSTR("Invalid argument type passed to exec().")));
    }
}

//! JSPDO.lastInsertId() impl.
v8::Handle<v8::Value> JSPDO_lastInsertId( v8::Arguments const & argv )
{
    ASSERT_DRV_DECL(argv.This());
    std::string const hint = (argv.Length()>0)
        ? cv::JSToStdString(argv[0])
        : std::string();
    return cv::CastToJS( drv->last_insert_id( hint.empty() ? NULL : hint.c_str() ) );
}

//! JSPDO.driverList generator.
v8::Local<v8::Array> JSPDO_driverList()
{
    char const * const * dlist = cpdo_available_drivers();
    v8::Local<v8::Array> ar( v8::Array::New() );
    uint32_t ndx = 0;
    for( ; *dlist; ++dlist )
    {
        ar->Set( ndx++, v8::String::New(*dlist) );
    }
    return ar;
}

#if 1
//! For internal use by the bindings init code.
static void ReportException(v8::TryCatch* try_catch, std::ostream & out) {
    // code taken from v8 sample shell
  v8::HandleScope handle_scope;
  //v8::String::Utf8Value exception();
  std::string exception_string( cv::CastFromJS<std::string>(try_catch->Exception()) ) ;
  v8::Handle<v8::Message> message = try_catch->Message();
  if (message.IsEmpty()) {
      // V8 didn't provide any extra information about this error; just
      // print the exception.
      out << exception_string << '\n';
  } else {
    // Print (filename):(line number): (message).
    std::string filename_string = cv::JSToStdString(message->GetScriptResourceName());
    int linenum = message->GetLineNumber();
    out << filename_string << ':' << linenum
         << ": "<< exception_string
         << '\n';
    // Print line of source code.
    std::string sourceline_string = cv::JSToStdString(message->GetSourceLine());
    out << sourceline_string << '\n';
    // Print wavy underline (GetUnderline is deprecated).
    int start = message->GetStartColumn();
    for (int i = 0; i < start; i++) {
        out << ' ';
    }
    int end = message->GetEndColumn();
    for (int i = start; i < end; i++) {
        out << '^';
    }
    out << std::endl;
    v8::String::Utf8Value stack_trace(try_catch->StackTrace());
    if (stack_trace.length() > 0) {
        std::string stack_trace_string = cv::JSToStdString(try_catch->StackTrace());
        out << stack_trace_string << '\n';
    }
  }
}

#endif

namespace {
#include "jspdo-init.cpp" /* generated code (JavaScript source) */
}

/**
    This is run during the binding setup to install JSPDO functions which
    are much easier to implement in JS code (and are thus implemented in JS
    code which gets compiled into jspdo-init.cpp during the build process).

    This function reads the contents of the global var jspdoInitCode, which
    is assumed to be defined in jspdo-init.cpp (which is assumed to be
    generated from jspdo-init.js using js2c.c (or equivalent)) and executes
    them. The init code is required to dereference an anonymous Function as
    the final operation in the init code. This function (the "return" value
    of the init code) will be called and ctor will be the 'this' object in
    that call. Inside that function, this.prototype will refer to the JSPDO
    prototype object. Thus 'this' and this.prototype can be used in the init
    code to extend the functionality of the ctor object (the JSPDO class'
    constructor).

    If the JS init code fails to compile or throws an exception, the binding
    process is aborted and a std::exception is thrown to report the error to
    the client. Since the JS-side init code gets compiled in to this binary,
    such an error should only ever happen during development of jspdo-init.js.

    This is called at the end of the binding process, meaning the ctor is
    completely set up at that point with all member functions and whatnot
    (except for those which are added by the init code, of course).
*/
static void JSPDO_extendCtor( v8::Handle<v8::Function> & ctor )
{
    v8::HandleScope scope;
    char const * fname = "jspdo-init.js";
    v8::Handle<v8::String> source( v8::String::New(jspdoInitCode, sizeof(jspdoInitCode)-1) );
    v8::TryCatch tc;
    v8::Handle<v8::Script> script = v8::Script::New(source, JSTR(fname));
    if (script.IsEmpty()) {
        std::ostringstream msg;
        msg << "Compilation of "<<JSPDO_CLASS_NAME<<" JS extensions failed: ";
        ReportException( &tc, msg );
        throw std::runtime_error( msg.str().c_str() );
    }

    v8::Handle<v8::Value> result = script->Run();
    if (result.IsEmpty()) {
        std::ostringstream msg;
        msg << "Execution of "<<JSPDO_CLASS_NAME<<" JS extensions failed: ";
        ReportException( &tc, msg );
        throw std::runtime_error( msg.str().c_str() );
    }
    assert( result->IsFunction() );
    v8::Handle<v8::Function> initFunc( v8::Function::Cast(*result) );
    v8::Local<v8::Value> self( ctor->GetPrototype() );
    v8::Handle<v8::Value> rc = initFunc->Call( ctor, 0, NULL );
    if( rc.IsEmpty() )
    {
        std::ostringstream msg;
        msg << "Got exception from "<<JSPDO_CLASS_NAME<<" JS init code: ";
        ReportException( &tc, msg );
        throw std::runtime_error( msg.str().c_str() );
    }
}

namespace cvv8 {

    v8::Handle<v8::Value> readFileContents( char const * fname, bool asByteArray )
    {
        if( ! fname || !*fname ) return Toss("File name may not be empty.");
        std::ifstream istr(fname, std::ios_base::binary/*needed(?) for Windows?*/);
        if( ! istr.good() ) return Toss(StringBuffer()<<
            "Could not open file ["
            << fname << "] for reading.");
        istr >> std::noskipws;
        std::ostringstream buf;
        std::copy( std::istream_iterator<char>(istr), std::istream_iterator<char>(),
                    std::ostream_iterator<char>(buf) );
        std::string const & s( buf.str() );
        if( s.empty() ) return v8::Null();
        else
        {
            if( asByteArray )
            {
                typedef cv::ClassCreator<JSByteArray> BAC;
                JSByteArray * ba = NULL;
                v8::Handle<v8::Object> baObj( BAC::Instance().NewInstance( 0, NULL, ba ) );
                if( baObj.IsEmpty() ) return v8::Undefined() /* assume exception is propagating. */;
                if( ! ba ) return cv::Toss("Allocation of ByteArray failed.");
                ba->append( s.data(), s.size() );
                return baObj;
            }
            else
            {
                return v8::String::New(s.c_str());
            }
        }
    }

    v8::Handle<v8::Value> readFileContents( char const * fname )
    {
        return readFileContents( fname, false );
    }

    template <>
    struct ClassCreator_SetupBindings<cpdo::driver>
    {
        static void SetupBindings( v8::Handle<v8::Object> const & dest )
        {
            using namespace v8;
            HandleScope hscope;
            //CERR << "Binding cpdo::driver...\n";
            ////////////////////////////////////////////////////////////
            // Bootstrap class-wrapping code...
            typedef cpdo::driver DRV;
            typedef cv::ClassCreator<DRV> WDRV;
            typedef cpdo::statement ST;
            typedef cv::ClassCreator<ST> WST;
            WDRV & wdrv( WDRV::Instance() );
            if( wdrv.IsSealed() )
            {
                wdrv.AddClassTo( JSPDO_CLASS_NAME, dest );
                return;
            }
            WST & wst( WST::Instance() );
            assert( ! wst.IsSealed() );

            if(0)// just an experiment
            {
                typedef cv::FunctionPtr< int(char const *), ::puts> FPPuts;
                FPPuts::Function("Hi, world.");
                typedef cv::InCaCatcher_std< InCaToInCa<Statement_stepArray>, std::logic_error > LECatch;
                typedef cv::InCaCatcher_std< LECatch, std::runtime_error > RECatch;
                typedef cv::InCaCatcher_std< RECatch > BaseCatch;
                v8::InvocationCallback cb;
                cb = BaseCatch::Call;
            }

            ////////////////////////////////////////////////////////////////////////
            // cpdo::statement bindings...
#define CATCHER cv::InCaCatcher_std
            Handle<ObjectTemplate> const & stProto( wst.Prototype() );
            wst("finalize", WST::DestroyObjectCallback )
                ("step", CATCHER< cv::MethodToInCa<ST, bool (),&ST::step> >::Call)
                ("stepArray", CATCHER< cv::InCaToInCa<Statement_stepArray> >::Call)
                ("stepObject", CATCHER< cv::InCaToInCa<Statement_stepObject> >::Call)
                ("columnName", CATCHER< cv::MethodToInCa<ST, char const * (uint16_t),&ST::col_name> >::Call )
                ("columnType", CATCHER< cv::MethodToInCa<ST, cpdo_data_type (uint16_t),&ST::col_type> >::Call )
                ("get", CATCHER< cv::InCaToInCa<Statement_get> >::Call )
                ("bind", CATCHER< cv::InCaToInCa<Statement_bind> >::Call)
                ("reset", CATCHER< cv::MethodToInCa<ST, void (void),&ST::reset> >::Call)
                ("toString", CATCHER< cv::InCaToInCa<Statement_toString> >::Call )
                ("paramIndex", MethodToInCa<ST, uint16_t (char const *),&ST::param_index>::Call /* doesn't throw */ )
                ("paramName", CATCHER<cv::MethodToInCa<ST, char const *(uint16_t),&ST::param_name> >::Call )
                ;

            v8::AccessorSetter const throwOnSet = ThrowingSetter::Set;
            //SPB::BindGetterMethod<std::string (),&ST::error_text>( "errorText", stProto );
            //SPB::BindGetterMethod<int (),&ST::error_code>( "errorCode", stProto );
            //SPB::BindGetterMethod<uint16_t (),&ST::param_count>( "paramCount", stProto );
            //SPB::BindGetterMethod<uint16_t (),&ST::col_count>( "columnCount", stProto );
            stProto->SetAccessor(JSTR("errorCode"),
                                 MethodToGetter<ST, int (),&ST::error_code>::Get,
                                 throwOnSet);
            stProto->SetAccessor(JSTR("errorText"),
                                 MethodToGetter<ST, std::string (),&ST::error_text>::Get,
                                 throwOnSet);
            stProto->SetAccessor(JSTR("columnCount"),
                                 MethodToGetter<ST, uint16_t (),&ST::col_count>::Get,
                                 throwOnSet);
            stProto->SetAccessor(JSTR("paramCount"),
                                 MethodToGetter<ST, uint16_t (),&ST::param_count>::Get,
                                 throwOnSet);
            stProto->SetAccessor(JSTR("columnNames"), Statement_getColumnNames, throwOnSet );
            // do not bind columnTypes for the time being because
            // the same column in different rows CAN have different
            // types (this is how we know if a field is NULL).
            // stProto->SetAccessor(JSTR("columnTypes"), Statement_getColumnTypes, throwOnSet );
            stProto->SetAccessor(JSTR("paramNames"), Statement_getParamNames, throwOnSet );
            ////////////////////////////////////////////////////////////////////////
            // cpdo::driver bindings...
            Handle<ObjectTemplate> const & dProto( wdrv.Prototype() );
            wdrv("close", WDRV::DestroyObjectCallback )
                ("begin", CATCHER< cv::MethodToInCa<DRV,void (),&DRV::begin> >::Call )
                ("commit", CATCHER< cv::MethodToInCa<DRV,void (),&DRV::commit> >::Call )
                ("rollback", CATCHER< cv::MethodToInCa<DRV,void (),&DRV::rollback> >::Call)
                ("exec", CATCHER< cv::MethodToInCa<DRV,void (std::string const &),&DRV::exec> >::Call)
                ("prepare", CATCHER< cv::InCaToInCa<JSPDO_prepare> >::Call )
                ("exec", CATCHER< cv::InCaToInCa<JSPDO_exec> >::Call )
                ("lastInsertId",
                 CATCHER< cv::InCaToInCa<JSPDO_lastInsertId> >::Call
                 //LastInsId::Call
                 )
                ("toString", CATCHER< cv::InCaToInCa<JSPDO_toString> >::Call)
                ;
#undef CATCHER
            
            dProto->SetAccessor(JSTR("driverName"),
                                cv::ConstMethodToGetter<DRV, char const * (),&DRV::driver_name >::Get,
                                throwOnSet);
            dProto->SetAccessor(JSTR("errorText"),
                                cv::MethodToGetter<DRV, std::string (),&DRV::error_text >::Get,
                                throwOnSet);
            dProto->SetAccessor(JSTR("errorCode"),
                                cv::MethodToGetter<DRV, int (),&DRV::error_code >::Get,
                                throwOnSet);

            ////////////////////////////////////////////////////////////////////////
            // The following changes have to be made after the
            // prototype-level changes are made or they have no
            // effect. Once CtorFunction() is called, the prototype object
            // is effectively "sealed" - further changes made here won't show up
            // in new JS instances.
            v8::Handle<v8::Function> dCtor = wdrv.CtorFunction();
            JSByteArray::SetupBindings( dCtor );
            /**
               We don't want clients to instantiate Statement objects
               except via JSPDO.prepare(). So we don't add its
               constructor to the destination object, but we do store
               it internally in a hidden field so that we can be 100%
               certain (i hope!) v8 doesn't GC it.

               On second thought - if it's private then clients cannot do
               'instanceof' checks on it.
             */
            //dCtor->SetHiddenValue( JSTR("$Statement"), wst.CtorFunction() );
            dCtor->Set( JSTR("Statement"), wst.CtorFunction() );
            dCtor->Set( JSTR("driverList"), JSPDO_driverList() );
            dCtor->Set( JSTR("enableDebug"), v8::False() );
            dCtor->SetName( JSTR(JSPDO_CLASS_NAME) );
            dCtor->Set(JSTR("enableDestructorDebug"),
                    cv::CastToJS(FunctionToInCa< void (bool), setEnableDestructorDebug>::Call) );
            dCtor->Set(JSTR("readFileContents"),
                        CastToJS(
                        ArityDispatchList< CVV8_TYPELIST((
                            FunctionToInCa< v8::Handle<v8::Value> (char const *),
                                            readFileContents>,
                            FunctionToInCa< v8::Handle<v8::Value> (char const *, bool),
                                            readFileContents>
                        ))>::Call) );
                    
            if(0)
            { /* the C++ API hides the cpdo_step_code values from the
                 client, changing the semantics of step()'s return value
                 vis-a-vis the C API.
              */
                v8::Handle<v8::Object> dstep( Object::New() );
                dCtor->Set(JSTR("stepCodes"),dstep);
                dstep->Set(JSTR("OK"), cv::CastToJS<int>(CPDO_STEP_OK) );
                dstep->Set(JSTR("DONE"), cv::CastToJS<int>(CPDO_STEP_DONE) );
                dstep->Set(JSTR("ERROR"), cv::CastToJS<int>(CPDO_STEP_ERROR) );
            }


            { // Set up a map of cpdo_data_type enum entries...
                v8::Handle<v8::Object> dtypes( Object::New() );
                dCtor->Set(JSTR("columnTypes"),dtypes);
#define COLTYPE(X) dtypes->Set(JSTR(#X), Integer::New(CPDO_TYPE_##X))
                COLTYPE(ERROR);
                COLTYPE(NULL);
                COLTYPE(INT8);
                COLTYPE(INT16);
                COLTYPE(INT32);
                COLTYPE(INT64);
                COLTYPE(FLOAT);
                COLTYPE(DOUBLE);
                COLTYPE(STRING);
                COLTYPE(BLOB);
                COLTYPE(CUSTOM);
#undef COLTYPE
            }
            JSPDO_extendCtor( dCtor );
           
            ////////////////////////////////////////////////////////////////////////
            // Add the new class to the engine...
            wdrv.AddClassTo( JSPDO_CLASS_NAME, dest );
            //CERR << "Finished binding cpdo::driver.\n";
        }
    };

}


/**
   Pass the JS engine's global object (or a "virtual" global
   object of your choice) to add the JSPDO class to it.
*/
void cv::JSPDO::SetupBindings( v8::Handle<v8::Object> const & dest )
{
    cv::ClassCreator_SetupBindings<cpdo::driver>::SetupBindings(dest);
}

#undef ASSERT_ARGV
#undef DRV_DECL
#undef ASSERT_DRV_DECL
#undef STMT_DECL
#undef ASSERT_STMT_DECL
#undef JSTR
#undef CERR
#undef JSPDO_CLASS_NAME
