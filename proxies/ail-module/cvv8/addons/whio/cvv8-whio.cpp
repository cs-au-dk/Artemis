#include "cvv8-whio.hpp"
#include "bytearray.hpp"
#include "cvv8/XTo.hpp"
#include <cassert>
#include <cerrno>
#include <sstream>

#if defined(WIN32)
#  define USE_SIGNALS 0
#else
#  define USE_SIGNALS 1
#endif

#if USE_SIGNALS
#include <signal.h>
static void signal_ignore(int)
{
    /*
      Weird: if i don't install a signal handler, ctrl-c (SIGINT)
      kills my app violently during Socket.accept(), as would be expected. If
      i do install a handler then accept() returns with errno=EINTR.
    */
    //Toss("C signal caught!");
}
#endif
namespace {
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
}

#undef USE_SIGNALS

namespace cvv8 { 

    //CVV8_TypeName_IMPL((whio::IOBase),"IOBase");

    CVV8_TypeName_IMPL((whio::StreamBase),"StreamBase");
    CVV8_TypeName_IMPL((whio::InStream),"InStream");
    //CVV8_TypeName_IMPL((whio::FileInStream),"FileInStream");
    CVV8_TypeName_IMPL((whio::OutStream),"OutStream");
    //CVV8_TypeName_IMPL((whio::FileOutStream),"FileOutStream");

    CVV8_TypeName_IMPL((whio::IODev),"IODev");
    CVV8_TypeName_IMPL((whio::FileIODev),"FileIODev");
    CVV8_TypeName_IMPL((whio::MemoryIODev),"MemoryIODev");
    CVV8_TypeName_IMPL((whio::Subdevice),"Subdevice");
    CVV8_TypeName_IMPL((whio::EPFS::PseudoFile),"PseudoFile");

    CVV8_TypeName_IMPL((whio::EPFS),"EPFS");
    CVV8_TypeName_IMPL((io::ByteArrayIODev),"ByteArrayIODev");

namespace io {

    /**
       toString() impl for our various bound classes.
     */
    template <typename T>
    v8::Handle<v8::Value> toString_generic( v8::Arguments const & argv )
    {
        T const * self = CastFromJS<T>(argv.This());
        StringBuffer s;
        s << "[object "<<TypeName<T>::Value<<'@'
          << (void const *)self << ']';
        return s;
    }
    
    /**
       write() impl for whio::OutStream and whio::IODev.
     */
    template <typename OutType>
    whio_size_t write_impl( v8::Arguments const & argv )
    {
        int const argc = argv.Length();
        if( (0==argc) || (2 < argc) )
        {
            Toss("write() requires 1 or 2 arguments!");
            return 0;
        }
        OutType * os = CastFromJS<OutType>(argv.This());
        if( ! os )
        {
            std::ostringstream msg;
            msg << TypeName<OutType>::Value << "::write() could not find its native 'this' pointer.";
            throw std::runtime_error(msg.str());
        }
        v8::Handle<v8::Value> arg(argv[0]);
        if( arg->IsString() )
        {
            /*
              If we want to unlock while writing we have to copy the bytes
              somewhere outside of v8. We could theoretically get away
              with calling (*bytes) and passing that ref during our
              unlocked time, but that officially invokes undefined
              behaviour b/c v8 may move the memory around during gc.
            */
            v8::String::Utf8Value bytes(argv[0]);
            whio_size_t const blen = static_cast<whio_size_t>( bytes.length() );
            whio_size_t n = (argv.Length()>1)
                ? CastFromJS<whio_size_t>(argv[1])
                : blen
                ;
            if( n > blen ) n = blen;
            {
                errno = 0;
                CSignalSentry sigSentry;
                n = os->write( *bytes, n );
                // TODO: if errno indicates an interrupt,
                // Toss() here.
            }
            return n;
        }
        else
        {
            JSByteArray * ba = CastFromJS<JSByteArray>( arg );
            if( ! ba )
            {
                Toss("The first argument must be a String or ByteArray.");
                return 0;
            }
            whio_size_t const blen = static_cast<whio_size_t>( ba->length() );
            whio_size_t n;
            if( argv.Length() > 1 )
            {
                n = CastFromJS<whio_size_t>(argv[1]);
                if( n > blen ) n = blen;
            }
            else n = ba->length();
            {
                v8::Unlocker unl;
                errno = 0;
                CSignalSentry sigSentry;
                n = os->write( ba->rawBuffer(), n );
                // TODO: if errno indicates an interrupt,
                // Toss() here.
            }
            return n;
        }
    }

    /**
       read() impl for whio::InStream and whio::IODev.
    */
    template <typename InType>
    v8::Handle<v8::Value> read_impl( v8::Arguments const & argv )
    {
        int const argc = argv.Length();
        if( 2 != argc)
        {
            return Toss("read() requires exactly 2 arguments!");
        }
        InType * is = CastFromJS<InType>(argv.This());
        if( ! is )
        {
            std::ostringstream os;
            os << TypeName<InType>::Value << "::read() could not find its native 'this' pointer.";
            throw std::runtime_error(os.str());
        }
        whio_size_t n = CastFromJS<whio_size_t>(argv[0]);
        if( ! n ) return v8::Null();
        typedef std::vector<unsigned char> VT;
        VT vec(n,'\0');
        whio_size_t rc;
        {
            v8::Unlocker unl;
            CSignalSentry csig;
            errno = 0;
            rc = is->read( &vec[0], static_cast<whio_size_t>(vec.size()) );
            /*
              TODO: if errno indicates an interrupt, throw here.
            */
        }
        if( ! rc ) return v8::Null();
        vec.resize(rc);
        bool const binary = argv[1]->BooleanValue();
        if( binary )
        {
            typedef ClassCreator<JSByteArray> CW;
            JSByteArray * ba = NULL;
            v8::Handle<v8::Object> jba = CW::Instance().NewInstance( 0, NULL, ba );
            if( ! ba )
            {
                return Toss("Creation of ByteArray object failed!");
            }
            ba->swapBuffer( vec );
            return jba;
        }
        else
        {
            return v8::String::New( (char const *)&vec[0], static_cast<int>( vec.size() ) );
        }
    }

    /**
       FIXME: we can consolidate InStream_GZipTo/GUnzipTo/CopyTo into a single
       template, i think.
    */
    v8::Handle<v8::Value> InStream_GZipTo( v8::Arguments const & argv )
    {
        typedef whio::InStream ST;
        char const * fname = "gzipTo";
        if( argv.Length() < 1 )
        {
            invalid_arg:
            return Toss(StringBuffer()
                        << TypeName<ST>::Value
                        << "::"<<fname<<"() signature: "
                        << "("<<TypeName<whio::OutStream>::Value
                        << "|"<<TypeName<whio::IODev>::Value
                        <<" [, int level=3])");
        }
        ST * src = CastFromJS<ST>(argv.This());
        if( ! src )
        {
            return Toss(StringBuffer()
                        << TypeName<ST>::Value
                        << "::"<<fname<<"() could not find native 'this' pointer.");
        }
        whio::OutStream * destS = CastFromJS<whio::OutStream>(argv[0]);
        whio::IODev * destD = destS ? NULL : CastFromJS<whio::IODev>(argv[0]);
        if( !destS && !destD )
        {
            goto invalid_arg;
        }
        int const level = (argv.Length()>1)
            ? CastFromJS<int>(argv[1])
            : 3;
        int rc;
        if( destS )
        {
            rc = whio_stream_gzip( src->handle(), destS->handle(), level );
        }
        else
        {
            assert( NULL != destD );
            whio::OutStream dest( *destD, false );
            assert( dest.handle() );
            rc = whio_stream_gzip( src->handle(), dest.handle(), level );
        }
        if( rc )
        {
            return Toss(StringBuffer()
                        << TypeName<ST>::Value
                        << "::"<<fname<<"(): whio_stream_gzip() failed with code "
                        << rc << '.');
        }
        else return v8::Undefined();
    }

    v8::Handle<v8::Value> InStream_GUnzipTo( v8::Arguments const & argv )
    {
        typedef whio::InStream ST;
        char const * fname = "gunzipTo";
        if( argv.Length() < 1 )
        {
            invalid_arg:
            return Toss(StringBuffer()
                        << TypeName<ST>::Value
                        << "::"<<fname<<"() signature: "
                        << "("<<TypeName<whio::OutStream>::Value
                        << "|"<<TypeName<whio::IODev>::Value
                        << ")");
        }
        ST * src = CastFromJS<ST>(argv.This());
        if( ! src )
        {
            return Toss(StringBuffer()
                        << TypeName<ST>::Value
                        << "::"<<fname<<"() could not find native 'this' pointer.");
        }
        whio::OutStream * destS = CastFromJS<whio::OutStream>(argv[0]);
        whio::IODev * destD = destS ? NULL : CastFromJS<whio::IODev>(argv[0]);
        if( ! destS && !destD )
        {
            goto invalid_arg;
        }
        int rc;
        if( destS )
        {
            rc = whio_stream_gunzip( src->handle(), destS->handle() );
        }
        else
        {
            assert( NULL != destD );
            whio::OutStream dest( *destD, false );
            assert( dest.handle() );
            rc = whio_stream_gunzip( src->handle(), dest.handle() );
        }
        if( rc )
        {
            return Toss(StringBuffer()
                        << TypeName<ST>::Value
                        << "::"<<fname<<"(): whio_stream_gunzip() failed with code "
                        << rc << '.');
        }
        else return v8::Undefined();
    }

    v8::Handle<v8::Value> InStream_CopyTo( v8::Arguments const & argv )
    {
        typedef whio::InStream ST;
        char const * fname = "copyTo";
        if( argv.Length() != 1 )
        {
            invalid_arg:
            return Toss(StringBuffer()
                        << TypeName<ST>::Value
                        << "::"<<fname<<"() signature: "
                        << "("<<TypeName<whio::OutStream>::Value
                        << "|"<<TypeName<whio::IODev>::Value
                        << ")");
        }
        ST * src = CastFromJS<ST>(argv.This());
        if( ! src )
        {
            return Toss(StringBuffer()
                        << TypeName<ST>::Value
                        << "::"<<fname<<"() could not find native 'this' pointer.");
        }
        whio::OutStream * destS = CastFromJS<whio::OutStream>(argv[0]);
        whio::IODev * destD = destS ? NULL : CastFromJS<whio::IODev>(argv[0]);
        if( ! destS && !destD )
        {
            goto invalid_arg;
        }
        int rc;
        if( destS )
        {
            rc = whio_stream_copy( src->handle(), destS->handle() );
        }
        else
        {
            assert( NULL != destD );
            whio::OutStream dest( *destD, false );
            rc = whio_stream_copy( src->handle(), dest.handle() );
        }
        if( rc )
        {
            return Toss(StringBuffer()
                        << TypeName<ST>::Value
                        << "::"<<fname<<"(): whio_stream_copy() failed with rc "
                        << rc << " ("<<whio_rc_string(rc)<<")");
        }
        else return v8::Undefined();
    }


    void ByteArrayIODev::assertOpen() const
    {
        /** this function is never being called??? */
        this->MemoryIODev::assertOpen();
        if( ! m_ba ) throw std::runtime_error("Not connected to a ByteArray.");
        else if( m_origMem != m_ba->rawBuffer() )
        {
            throw std::runtime_error("ByteArray's buffer appears to have moved since this device was initialized.");
        }
    }

    ByteArrayIODev::~ByteArrayIODev()
    {}

    ByteArrayIODev::ByteArrayIODev( JSByteArray & ba, bool writeMode )
        : MemoryIODev( ba.rawBuffer(), ba.length() ),
          m_ba(&ba),
          m_origMem( ba.rawBuffer() )
    {
        if( writeMode )
        {
            whio_dev_memmap_remap( m_io, ba.rawBuffer(), ba.rawBuffer(), ba.length() );
        }
    }

    ByteArrayIODev::ByteArrayIODev( JSByteArray const & ba )
        : MemoryIODev( ba.rawBuffer(), ba.length() ),
          m_ba(&ba),
          m_origMem( ba.rawBuffer() )
    {
    }
    
}// namespace io


#if 0
    const void * ClassCreator_TypeID<whio::IODev>::Value = TypeName<whio::IODev>::Value;
    const void * ClassCreator_TypeID<whio::StreamBase>::Value = TypeName<whio::StreamBase>::Value;
#endif

    /**
       An arguments predicate which returns true if the argument at
       index I is one of the values SEEK_SET, SEEK_CUR, SEEK_END.
    */
    template <int I>
    struct ArgAt_IsWhence : ArgumentsPredicate
    {
        inline bool operator()( v8::Arguments const & args ) const
        {
            if( args.Length() <= I ) return false;
            
            else
            {
                v8::Handle<v8::Value> const & v(args[I]);
                if( ! ValIs<int32_t>()(v) ) return false;
                else switch( v->Int32Value() )
                {
                  case SEEK_SET:
                  case SEEK_CUR:
                  case SEEK_END:
                      return true;
                  default:
                      return false;
                }
            }
        }
    };
    
    void ClassCreator_SetupBindings<whio::IODev>::Initialize( v8::Handle<v8::Object> const & dest )
    {
        typedef whio::IODev IOD;
        typedef ClassCreator<IOD> CCDev;
        CCDev & cc(CCDev::Instance());
        if( cc.IsSealed() )
        {
            cc.AddClassTo(TypeName<IOD>::Value, dest);
            return;
        }

#define CATCHER InCaCatcher_std
        cc
            ("close", CCDev::DestroyObjectCallback )
            ("clearError",
             CATCHER< MethodTo<InCa, IOD, void (), &IOD::clearError> >::Call )
            ("error",
             CATCHER< MethodTo<InCa, IOD, int (), &IOD::error> >::Call )
            ("eof",
             CATCHER< MethodTo<InCa, IOD, bool (), &IOD::eof> >::Call )
            ("flush",
             CATCHER< MethodTo<InCa, IOD, void (), &IOD::flush> >::Call )
            ("iomode",
             CATCHER< MethodTo<InCa, IOD, whio_iomode_mask (), &IOD::iomode> >::Call )
            //("isClosed",
            // MethodTo<InCa, const IOD, bool (), &IOD::isClosed>::Call )
            ("read",
             CATCHER< InCaToInCa< io::read_impl<IOD> > >::Call )
            ("size",
             CATCHER< MethodTo<InCa, IOD, whio_size_t (), &IOD::size> >::Call )
            ("tell",
             CATCHER< MethodTo<InCa, IOD, whio_size_t (), &IOD::tell> >::Call )
            ("toString",
#if 0
            /* WTF?

               Error: symbol `_ZN4cvv86Detail14FunctionToInCaIFN2v86HandleINS2_5ValueEEERKNS2_9ArgumentsEEXadL_ZNS9_IN4whio5IODevEEES5_S8_EELb0EE4CallES8_' is already defined
            */
             InCaToInCa< io::toString_generic<IOD> >::Call
#else
             io::toString_generic<IOD>
#endif
             )
            ("truncate",
             CATCHER< MethodTo<InCa, IOD, void (whio_off_t), &IOD::truncate> >::Call )
            ("write",
             CATCHER< InCaLikeFunction<whio_size_t, io::write_impl<IOD> > >::Call )
            ;
        v8::Handle<v8::Function> seek =
            v8::FunctionTemplate::New(CATCHER<
               /*
                 Reminder to reader: this overly-complex seek()
                 binding is for argument-validation proof-of-concept
                 purposes, not because seek() needs to be overloaded
                 this way. We could just as easily bind directly to
                 seek() and the bound class would throw if JS code
                 passes in an invalid value. The pre-checking done
                 here is basically a demonstration of how we can
                 perform near-arbitrary type/range checking as a
                 precondition to calling a particular binding.
               */
               PredicatedInCaDispatcher< CVV8_TYPELIST((
                    PredicatedInCa< 
                    //Argv_AndN< CVV8_TYPELIST(( Argv_Length<2>, ArgAt_IsA<0,whio_off_t>, ArgAt_IsWhence<1> )) >,
                    // Equivalent:
                    Argv_And< Argv_Length<2>, Argv_And< ArgAt_IsA<0,whio_off_t>, ArgAt_IsWhence<1> > >,
                    MethodTo<InCa, IOD, whio_size_t (whio_off_t,int), &IOD::seek>
                    >
               )) >
            >::Call
            )->GetFunction();
#define SET(K) seek->Set(v8::String::NewSymbol(#K),v8::Integer::New(SEEK_##K))
        SET(SET);
        SET(CUR);
        SET(END);
#undef SET
        cc("seek",seek);

#undef CATCHER
        cc.AddClassTo(TypeName<IOD>::Value, dest);
        ClassCreator_SetupBindings<whio::MemoryIODev>::Initialize( dest );
        ClassCreator_SetupBindings<io::ByteArrayIODev>::Initialize( dest );
        ClassCreator_SetupBindings<whio::Subdevice>::Initialize( dest );
        return;
    }

    void ClassCreator_SetupBindings<whio::MemoryIODev>::Initialize( v8::Handle<v8::Object> const & dest )
    {
        typedef whio::MemoryIODev IOD;
        typedef ClassCreator<IOD> CC;
        CC & cc(CC::Instance());
        if( cc.IsSealed() )
        {
            cc.AddClassTo(TypeName<IOD>::Value, dest);
            return;
        }
        cc.Inherit<whio::IODev>();
        cc
            ("bufferSize",
             InCaCatcher_std< MethodTo<InCa, IOD, whio_size_t (), &IOD::bufferSize> >::Call )
            ("toString",
             io::toString_generic<IOD> )
            ;
        cc.AddClassTo(TypeName<IOD>::Value, dest);
    }

    void ClassCreator_SetupBindings<io::ByteArrayIODev>::Initialize( v8::Handle<v8::Object> const & dest )
    {
        typedef io::ByteArrayIODev IOD;
        typedef ClassCreator<IOD> CC;
        CC & cc(CC::Instance());
        if( cc.IsSealed() )
        {
            cc.AddClassTo(TypeName<IOD>::Value, dest);
            return;
        }
        cc.Inherit<whio::MemoryIODev>();
        cc
            ("toString",
             io::toString_generic<IOD> )
            ;
        cc.AddClassTo(TypeName<IOD>::Value, dest);
    }

    
    void ClassCreator_SetupBindings<whio::Subdevice>::Initialize( v8::Handle<v8::Object> const & dest )
    {
        typedef whio::Subdevice IOD;
        typedef ClassCreator<IOD> CC;
        CC & cc(CC::Instance());
        if( cc.IsSealed() )
        {
            cc.AddClassTo(TypeName<IOD>::Value, dest);
            return;
        }
        cc.Inherit<whio::IODev>();

        typedef PredicatedInCa< // rebound(uint,uint)
            Argv_TypesMatch< CVV8_TYPELIST((whio_size_t,whio_size_t)) >,
            MethodTo<InCa, IOD, void (whio_size_t,whio_size_t), &IOD::rebound>
        > Rebound2;
        typedef PredicatedInCa< // rebound(IODev,uint,uint)
            Argv_TypesMatch< CVV8_TYPELIST((whio::IODev &, whio_size_t,whio_size_t)) >,
            MethodTo<InCa, IOD, void (whio::IODev &, whio_size_t,whio_size_t), &IOD::rebound>
        > Rebound3;
        typedef PredicatedInCaDispatcher< CVV8_TYPELIST(( Rebound2, Rebound3 )) > Rebound;
        cc
            ("rebound",
             InCaCatcher_std< Rebound >::Call )
            ("toString",
             io::toString_generic<IOD> )
            ;
        cc.AddClassTo(TypeName<IOD>::Value, dest);
    }
    
    void ClassCreator_SetupBindings<whio::StreamBase>::Initialize( v8::Handle<v8::Object> const & dest )
    {
        typedef whio::StreamBase ST;
        typedef ClassCreator<ST> CC;
        CC & cc(CC::Instance());
        if( cc.IsSealed() )
        {
            cc.AddClassTo(TypeName<ST>::Value, dest);
            return;
        }

#define CATCHER InCaCatcher_std
        cc
            ("close", CC::DestroyObjectCallback )
            ("isGood",
             CATCHER< MethodTo<InCa, ST, bool (), &ST::isGood> >::Call )
            ("iomode",
             CATCHER< MethodTo<InCa, ST, whio_iomode_mask (), &ST::iomode> >::Call )
            //("isClosed",
            // MethodTo<InCa, const ST, bool (), &ST::isClosed>::Call )
            ("toString",
             io::toString_generic<ST>)
            ;
#undef CATCHER
        cc.AddClassTo(TypeName<ST>::Value, dest);
        return;
    }
    

    void ClassCreator_SetupBindings<whio::OutStream>::Initialize( v8::Handle<v8::Object> const & dest )
    {
        typedef whio::OutStream ST;
        typedef ClassCreator<ST> CC;
        CC & cc(CC::Instance());
        if( cc.IsSealed() )
        {
            cc.AddClassTo(TypeName<ST>::Value, dest);
            return;
        }

        cc.Inherit<whio::StreamBase>();
#define CATCHER InCaCatcher_std
        cc
            ("flush",
             CATCHER< MethodTo<InCa, ST, void (), &ST::flush> >::Call )
            ("toString",
             io::toString_generic<ST>)
            ("write",
             CATCHER< InCaLikeFunction<whio_size_t, io::write_impl<ST> > >::Call )
            ;
#undef CATCHER
        cc.AddClassTo(TypeName<ST>::Value, dest);
        return;
    }

    void ClassCreator_SetupBindings<whio::InStream>::Initialize( v8::Handle<v8::Object> const & dest )
    {
        typedef whio::InStream ST;
        typedef ClassCreator<ST> CC;
        CC & cc(CC::Instance());
        if( cc.IsSealed() )
        {
            cc.AddClassTo(TypeName<ST>::Value, dest);
            return;
        }
        cc.Inherit<whio::StreamBase>();
#define CATCHER InCaCatcher_std
        cc
            ("gzipTo", io::InStream_GZipTo )
            ("gunzipTo", io::InStream_GUnzipTo )
            ("copyTo", io::InStream_CopyTo )
            ("read",
             CATCHER< InCaToInCa< io::read_impl<ST> > >::Call )
            ("toString",
             io::toString_generic<ST>)
            ;
#undef CATCHER
        cc.AddClassTo(TypeName<ST>::Value, dest);
        return;
    }

    
    v8::Handle<v8::Value> NativeToJS<whio_epfs_fsopt>::operator()( whio_epfs_fsopt const & opt ) const
    {
        v8::Handle<v8::Object> const & obj( v8::Object::New() );
#define JSTR v8::String::NewSymbol
        obj->Set(JSTR("blockSize"), v8::Integer::NewFromUnsigned(opt.blockSize));
        obj->Set(JSTR("inodeCount"), v8::Integer::NewFromUnsigned(opt.inodeCount));
        obj->Set(JSTR("maxBlocks"), v8::Integer::NewFromUnsigned(opt.maxBlocks));
#undef JSTR
        return obj;
    }

    whio_epfs_fsopt JSToNative<whio_epfs_fsopt>::operator()( v8::Handle<v8::Value> const & h ) const
    {
        whio_epfs_fsopt rc = whio_epfs_fsopt_empty;
        if( ! h->IsObject() ) return rc;
        else
        {
#define JSTR v8::String::NewSymbol
            v8::Handle<v8::Object> obj( v8::Object::Cast(*h) );
            v8::Handle<v8::Value> v;
#define GET(K,T) v = obj->Get(JSTR(#K));                 \
            if( !v.IsEmpty() ) rc.K = static_cast< T >(v->Uint32Value())

            GET(blockSize,whio_size_t);
            GET(inodeCount,whio_epfs_id_t);
            GET(maxBlocks,whio_epfs_id_t);
#undef GET
#undef JSTR
            return rc;
        }
    }



    v8::Handle<v8::Value> EPFS_OpenPseudoFile( v8::Arguments const & argv )
    {
        if( argv.Length() != 2 )
        {
            StringBuffer msg;
            msg << TypeName<whio::EPFS>::Value<< "::open() "
                << "requires exactly 2 arguments.";
            return Toss(msg.toError());
        }
        else
        {
            v8::Handle<v8::Value> av[] = {
            argv.This(),
            argv[0],
            argv[1]
            };
            typedef ClassCreator<whio::EPFS::PseudoFile> CC;
            return CC::Instance().NewInstance(3, av);
        }
    }

    struct ForeachInode
    {
        v8::Local<v8::Function> func;
        v8::Handle<v8::Object> self;
        v8::Handle<v8::Value> data;
        whio::EPFS * fs;
        ForeachInode() : func(),
                         self(),
                         data(v8::Undefined()),
                         fs(NULL)
        {}
    };

    static v8::Handle<v8::Object> InodeToObject( whio_epfs_inode const * i )
    {
        v8::Handle<v8::Object> o( v8::Object::New() );
#define SET(K,V) o->Set(v8::String::NewSymbol(K), V)
        SET("id",CastToJS(i->id));
        SET("mtime",CastToJS(i->mtime));
        SET("size",CastToJS(i->size));
        //SET("flags",CastToJS(i->flags));
        SET("clientFlags",CastToJS(i->cflags));
        //SET("firstBlock",CastToJS(i->firstBlock));
#undef SET
        return o;
    }

    static int ForeachInode_callback( whio_epfs * fs, whio_epfs_inode const * ent, void * clientData )
    {
        ForeachInode * fi = (ForeachInode *)clientData;
        v8::Handle<v8::Object> idata = InodeToObject(ent);
        if( whio_epfs_has_namer(fs) )
        {
            idata->Set(v8::String::NewSymbol("name"),
                       CastToJS( fi->fs->name( ent->id ) ) );
        }
        v8::Handle<v8::Value> av[] = {
            idata,
            fi->data
        };
        v8::Handle<v8::Value> const & rc( fi->func->Call( fi->self, 2, av ) );
        // How to tell if v8 threw here?
        return CastFromJS<int>(rc);
    }

    v8::Handle<v8::Value> EPFS_ForEachInode( v8::Arguments const & argv )
    {
        /**
           foreachInode( function(inode,data) {} )
        */
        typedef whio::EPFS FS;
        FS * fs = CastFromJS<FS>(argv.This());
        if( ! fs )
        {
            return Toss(StringBuffer()
                        << TypeName<FS>::Value
                        << "::foreachInode() could not find native 'this' pointer.");
        }
        ForeachInode fi;
        v8::Handle<v8::Function> jf;
        v8::Handle<v8::Value> a1(argv[0]);
        if( (argv.Length()<1) || !a1->IsFunction() )
        {
            return Toss(StringBuffer()
                        << TypeName<FS>::Value
                        << "::foreachInode() requires a Function as its first argument.");
        }
        else
        {
            fi.func = v8::Function::Cast(*a1);
        }
        fi.fs = fs;
        fi.self = argv.This();
        if( argv.Length() > 1 ) fi.data = argv[1];
        int const rc = whio_epfs_foreach_inode( fs->handle(), NULL, NULL,
                                                ForeachInode_callback, &fi );
        return CastToJS( rc );
    }

    static v8::Handle<v8::Value> GetEpfsVersionInfo()
    {
        v8::Handle<v8::Object> rc( v8::Object::New() );
        const uint16_t * mb = whio_epfs_magic_bytes;
#define SET(K,I) rc->Set(v8::String::NewSymbol(K), CastToJS(mb[I]))
        SET("year",0);
        SET("month",1);
        SET("day",2);
        SET("sizeTBits",3);
        SET("idTBits",4);
        SET("maxLabelLength",5);
        SET("sizeOfNamerLabel",6);
#undef SET
        return rc;
    }
    
    void ClassCreator_SetupBindings<whio::EPFS>::Initialize( v8::Handle<v8::Object> const & dest )
    {
        typedef whio::EPFS T;
        typedef ClassCreator<T> CC;
        CC & cc(CC::Instance());
        if( cc.IsSealed() )
        {
            cc.AddClassTo(TypeName<T>::Value, dest);
            return;
        }


#define CATCHER InCaCatcher_std
        typedef CATCHER< ArityDispatchList< CVV8_TYPELIST((
                      // label getter
                      MethodTo<InCa, T, std::string (), &T::label>,
                      // label setter
                      MethodTo<InCa, T, void (char const *), &T::label>
                      )) >
            > LabelFunc;
        v8::Handle<v8::Function> labelF( v8::FunctionTemplate::New(LabelFunc::Call)->GetFunction() );
        labelF->Set( v8::String::NewSymbol("maxLength"),
                     CastToJS<int>( whio_epfs_sizeof_label_payload ) );

        cc
            ("close", CC::DestroyObjectCallback )
            ("isRW",
             CATCHER< MethodTo<InCa, const T, bool (), &T::isRW> >::Call )
            //("isClosed",
            // MethodTo<InCa, const T, bool (), &T::isClosed>::Call )
            ("foreachInode",
             InCaToInCa< EPFS_ForEachInode >::Call)
	  /* potential fixme: set fsOptions as an Object (not
	     Function) right after construction. We don't want
	     MethodTo<Getter> here because of the computational cost
	     of the conversion (which i like to stress to the client
	     by making him use a function.
	  */
            ("fsOptions",
             MethodTo<InCa, const T, whio_epfs_fsopt const * (), &T::fsopt >::Call )
            ("hasNamer",
             CATCHER< MethodTo<InCa, const T, bool (), &T::hasNamer> >::Call )
            ("inodeId",
             CATCHER< MethodTo<InCa, T, whio_epfs_id_t (char const *name), &T::inodeId> >::Call )
            ("installNamer",
             CATCHER< MethodTo<InCa, T, void (char const *name), &T::installNamer> >::Call )
            ("label", labelF )
            ("name",
             CATCHER< ArityDispatchList<
             CVV8_TYPELIST((
                            MethodTo<InCa, T, std::string (whio_epfs_id_t), &T::name>,
                            MethodTo<InCa, T, void (whio_epfs_id_t, char const *), &T::name>
                            )) >
             >::Call)
            ("size",
             CATCHER< MethodTo<InCa, T, whio_size_t (), &T::size> >::Call )
            ("toString",
             io::toString_generic<T>)
            ("unlink",
             CATCHER< PredicatedInCaDispatcher< CVV8_TYPELIST((
                // unlink(id):
                PredicatedInCa< ArgAt_IsA<0,whio_epfs_id_t>,
                                MethodTo< InCa, T, void (whio_epfs_id_t), &T::unlink> >,
                // unlink(name):
                PredicatedInCa< ArgAt_IsA<0,v8::String>,
                                MethodTo< InCa, T, void (char const *), &T::unlink> >
                ))> >::Call)
            ("open",
             CATCHER< InCaToInCa<EPFS_OpenPseudoFile> >::Call)
            ;
#undef CATCHER
        v8::Handle<v8::Function> ctor( cc.CtorFunction() );
        ctor->Set( v8::String::NewSymbol("versionInfo"), GetEpfsVersionInfo() );
        ClassCreator<whio::EPFS::PseudoFile>::SetupBindings( ctor );
        cc.AddClassTo(TypeName<T>::Value, dest);
        return;
    }

    whio::EPFS * ClassCreator_Factory<whio::EPFS>::Create( v8::Persistent<v8::Object> &, v8::Arguments const & argv )
    {
        int const argc = argv.Length();
        if( (argc != 2) && (argc != 3) )
        {
            std::ostringstream os;
            os << TypeName<whio::EPFS>::Value
               << " ctor requires 2 or 3 arguments.";
            throw std::runtime_error(os.str());
        }
        bool const a2 = argv[1]->BooleanValue();
        v8::Handle<v8::Value> a1( argv[0] );
        ArgCaster<char const *> acName;
        char const * fname = NULL;
        whio::IODev * dev = NULL;
        whio::EPFS * fs = NULL;
        if( a1->IsString() )
        {
            v8::Handle<v8::String> fnStr( a1->ToString() );
            fname = acName.ToNative( a1 );
        }
        else
        {
            dev = CastFromJS<whio::IODev>(a1);
        }
        if( (!fname || !*fname) && !dev )
        {
            std::ostringstream os;
            os << TypeName<whio::EPFS>::Value
               << " ctor requires either a String or "
               << TypeName<whio::IODev>::Value
               << " as its first argument.";
            throw std::runtime_error(os.str());
        }
        typedef ClassCreator<whio::IODev> CCDev;
        if( 2 == argc )
        {/* openfs() */
            if( dev )
            {/* (IODev,bool) */
                fs = new whio::EPFS( dev->handle(), a2/*take ownership*/ );
                if( a2 )
                {
                    CCDev::DestroyObject(a1);
                }
            }
            else
            { /* (String,bool) */
                fs = new whio::EPFS(fname, a2/* write mode */);
            }
            return fs;
        }
        else
        { /* mkfs() */
            assert( 3 == argc );
            whio_epfs_fsopt fopt = CastFromJS<whio_epfs_fsopt>(argv[2]);
            if( ! fopt.inodeCount ) fopt.inodeCount = 512;
            if( ! fopt.blockSize ) fopt.blockSize = 1024 * 16;
            if( dev )
            {
                fs = new whio::EPFS( dev->handle(), a2/*take ownership*/, &fopt );
                if( a2 )
                {
                    CCDev::DestroyObject(a1);
                }
            }
            else
            {
                fs = new whio::EPFS(fname, a2/*allowOverwrite*/, &fopt);
            }
            return fs;
        }
    }

    void ClassCreator_Factory<whio::EPFS>::Delete( whio::EPFS * obj )
    {
        delete obj;
    }

    whio::EPFS::PseudoFile * ClassCreator_Factory<whio::EPFS::PseudoFile>::Create( v8::Persistent<v8::Object> &, v8::Arguments const & argv )
    {
        typedef whio::EPFS::PseudoFile T;
        if( 3 != argv.Length() )
        {
            std::ostringstream os;
            os << TypeName<T>::Value << " ctor requires 3 arguments.";
            throw std::runtime_error(os.str());
        }
        whio::EPFS * fs = CastFromJS<whio::EPFS>(argv[0]);
        if( !fs )
        {
            std::ostringstream os;
            os << TypeName<T>::Value << " ctor was passed a non-"
               << TypeName<whio::EPFS>::Value << " as the first argument.";
            throw std::runtime_error(os.str());
        }
        v8::Handle<v8::Value> a2( argv[1] );
        whio_iomode_mask mask = CastFromJS<whio_iomode_mask>(argv[2]);
        if( a2->IsString() )
        {
            ArgCaster<char const *> ac;
            return fs->openByName( ac.ToNative(a2), mask );
        }
        else
        {
            return fs->openById( CastFromJS<whio_epfs_id_t>(a2), mask );
        }
    }

    void ClassCreator_Factory<whio::EPFS::PseudoFile>::Delete( whio::EPFS::PseudoFile * obj )
    {
        delete obj;
    }



    void PseudoFile_mtimeSetter( v8::Local< v8::String >, v8::Local< v8::Value > time, const v8::AccessorInfo &info)
    {
        typedef whio::EPFS::PseudoFile T;
        uint32_t tv = (uint32_t)-1;
        T * p = CastFromJS<T>(info.This());
        if( ! p )
        {
            Toss(StringBuffer()
                 <<"Could not find native "
                 << TypeName<T>::Value
                 << " 'this' pointer.");
        }
        if( time->IsDate() )
        {
            v8::Handle<v8::Date> d( v8::Date::Cast(*time) );
            tv = static_cast<uint32_t>( d->NumberValue() / 1000 );
        }
        else if( time->IsNumber() )
        {
            tv = time->Uint32Value();
        }
        p->touch( tv );
    }

    uint32_t PseudoFile_touch( v8::Arguments const & argv )
    {
        typedef whio::EPFS::PseudoFile T;
        uint32_t tv = (uint32_t)-1;
        v8::Handle<v8::Value> time;
        if( argv.Length() ) time = argv[0];
        T * p = CastFromJS<T>(argv.This());
        if( ! p )
        {
            Toss(StringBuffer()
                 <<"Could not find native "
                 << TypeName<T>::Value
                 << " 'this' pointer.");
        }
        if( ! time.IsEmpty() )
        {
            if( time->IsDate() )
            {
                v8::Handle<v8::Date> d( v8::Date::Cast(*time) );
                tv = static_cast<uint32_t>( d->NumberValue() / 1000 );
            }
            else if( time->IsNumber() )
            {
                tv = time->Uint32Value();
            }
        }
        p->touch( tv );
        return p->mtime();
    }
    
    void ClassCreator_SetupBindings<whio::EPFS::PseudoFile>::Initialize( v8::Handle<v8::Object> const & dest )
    {
        typedef whio::EPFS::PseudoFile T;
        typedef ClassCreator<T> CC;
        CC & cc(CC::Instance());
        if( cc.IsSealed() )
        {
            cc.AddClassTo(TypeName<T>::Value, dest);
            return;
        }
        cc.Inherit<whio::IODev>();
#define CATCHER InCaCatcher_std
        cc
            ("toString",
             io::toString_generic<T>)
            ("touch",
             InCaLikeFunction< uint32_t, PseudoFile_touch >::Call)
            ;
#undef CATCHER
        AccessorAdder acc( cc.Prototype() );
#define GCATCH GetterCatcher_std
#define SCATCH SetterCatcher_std
        acc
            ("clientFlags",
             GCATCH< MethodTo<Getter, T const, uint32_t (), &T::clientFlags> >::Get,
             SCATCH< MethodTo<Setter, T, void (uint32_t), &T::clientFlags> >::Set)
            ("mtime",
             GCATCH< MethodTo<Getter, T const, uint32_t (), &T::mtime> >::Get,
             SCATCH< SetterToSetter<PseudoFile_mtimeSetter> >::Set )
            ("inodeId",
             GCATCH< MethodTo<Getter, T const, whio_epfs_id_t (), &T::inodeId> >::Get,
             ThrowingSetter::Set)
            ("name",
             GCATCH< MethodTo<Getter, T, std::string (), &T::name> >::Get,
             SCATCH< MethodTo<Setter, T, void (char const *), &T::name> >::Set)
            ;
#undef GCATCH
#undef SCATCH
        cc.AddClassTo(TypeName<T>::Value, dest);
        return;
    }
    
    
namespace io {

    whio::MemoryIODev * Ctor_MemoryIODev::Call( v8::Arguments const &argv )
    {
        assert( Ctor_MemoryIODev()(argv) );
        uint32_t const sz = CastFromJS<uint32_t>(argv[0]);
        float const factor = (argv.Length()>1)
            ? CastFromJS<float>(argv[1])
            : 1.5;
        return new whio::MemoryIODev( sz, factor );
    }

    whio::Subdevice * Ctor_Subdevice::Call( v8::Arguments const & argv )
    {
        assert( Ctor_Subdevice()(argv) );
        whio::IODev * parent = CastFromJS<whio::IODev*>(argv[0]);
        assert( (NULL != parent) && "Argument validation should have failed!" );
        whio_size_t const low = CastFromJS<whio_size_t>(argv[1]);
        whio_size_t const high = CastFromJS<whio_size_t>(argv[2]);
        return new whio::Subdevice( *parent, low, high );
    }

    
    whio::FileIODev * Ctor_FileIODev::Call( v8::Arguments const & argv )
    {
        assert( Ctor_FileIODev()(argv) );
        ArgCaster<char const *> ac;
        char const * fn = ac.ToNative(argv[0]);
        if( !fn || !*fn )
        {
            throw new std::runtime_error("Filename ctor argument may not be empty.");
        }
        else if( 2 == argv.Length() )
        {// (String name, int|String mode)
            v8::Handle<v8::Value> const & a1( argv[1] );
            if( ValIs<v8::String>()( a1 ) )
            {
                ArgCaster<char const *> modeString;
                return new whio::FileIODev( fn, modeString.ToNative(a1) );
            }
            else
            {
                return new whio::FileIODev( fn, JSToInt32(a1) );
            }
        }
        else if( 3 == argv.Length() )
        {// (String name, int mode, ushort permissions)
            return new whio::FileIODev( fn,
                                        CastFromJS<int32_t>(argv[1]),
                                        CastFromJS<uint16_t>(argv[2]) );
        }
        else
        {
            throw std::runtime_error("Internal error: Ctor_IODev_File got arguments which should not have passed validation.");
        }
        return NULL /* cannot be reached but gcc apparently cannot see that. */;
    }

    whio::OutStream * Ctor_OutStream::Call( v8::Arguments const &argv )
    {
        assert( Ctor_OutStream()(argv) );
        v8::Handle<v8::Value> arg( argv[0] );
        if( ValIs<v8::String>()(arg) )
        { /* (String name, bool truncate) */
            ArgCaster<char const *> ac;
            char const * fileName = ac.ToNative(arg);
            return new whio::FileOutStream(fileName,
                                           JSToBool(argv[1]) );

        }
        else
        {/* (IODev ioDevice, bool takeOwnership) */
            whio::IODev * d = CastFromJS<whio::IODev>( arg );
            if( ! d )
            {
                throw std::runtime_error("Internal error: Ctor_OutStream got arguments which should not have passed validation.");
            }
            bool const take = JSToBool(argv[1]);
            whio::OutStream * rc = new whio::OutStream( *d, take );
            if( take )
            { /* d was disconnected from its handle by the ctor,
                 but now we apply slightly different ownership
                 semantics than for the C/C++ APIs...
              */
                typedef ClassCreator<whio::IODev> CCDev;
                CCDev::DestroyObject( arg );
            }
            return rc;
        }
    }

    whio::InStream * Ctor_InStream::Call( v8::Arguments const &argv )
    {
        assert( Ctor_InStream()(argv) );
        v8::Handle<v8::Value> arg( argv[0] );
        if( ValIs<v8::String>()(arg) )
        { /* (String name) */
            ArgCaster<char const *> ac;
            char const * fileName = ac.ToNative(arg);
            return new whio::FileInStream(fileName);
        }
        else
        {/* (IODev ioDevice, bool takeOwnership) */
            whio::IODev * d = CastFromJS<whio::IODev>( arg );
            if( ! d )
            {
                throw std::runtime_error("Internal error: Ctor_InStream got arguments which should not have passed validation.");
            }
            bool const take = JSToBool(argv[1]);
            whio::InStream * rc = new whio::InStream( *d, JSToBool(argv[1]) );
            if( take )
            { /* d was disconnected from its handle by the ctor,
                 but now we apply slightly different ownership
                 semantics than for the C/C++ APIs...
              */
                typedef ClassCreator<whio::IODev> CCDev;
                CCDev::DestroyObject( arg );
            }
            return rc;
        }
    }

    ByteArrayIODev * Ctor_ByteArrayIODev::Call( v8::Arguments const & argv )
    {
        assert( Ctor_ByteArrayIODev()(argv) );
        int const argc = argv.Length();
        typedef ByteArrayIODev T;
        if( argc < 1 )
        {
            invalid_arg:
            std::ostringstream os;
            os << TypeName<T>::Value << " ctor signature: ("
               << TypeName<JSByteArray>::Value
               << "[, bool writeMode])";
            throw std::runtime_error(os.str());
        }
        JSByteArray * ba = CastFromJS<JSByteArray>(argv[0]);
        if(!ba) goto invalid_arg;
        if( 1 == argc )
        {
            return new ByteArrayIODev( *ba );
        }
        else if( 2 == argv.Length() )
        {// (ByteArray, bool)
            return new ByteArrayIODev( *ba, argv[1]->BooleanValue() );
        }
        else
        {
            goto invalid_arg;
        }
        //return NULL /* cannot be reached but gcc apparently cannot see that. */;
    }

    
    void SetupBindings( v8::Handle<v8::Object> dest )
    {
        char const * nsName = "whio";
        v8::Handle<v8::Object> ioObj( v8::Object::New() );
#define JSTR(X) v8::String::NewSymbol(X)
#define JINT(X) v8::Integer::New(X)
#define SET(OBJ,K,V) OBJ->Set(JSTR(K), V)

        SET(ioObj,"SEEK_SET",JINT(SEEK_SET));
        SET(ioObj,"SEEK_CUR",JINT(SEEK_CUR));
        SET(ioObj,"SEEK_END",JINT(SEEK_END));

        // WHIO_MODE_xxx flags...
        v8::Handle<v8::Object> ioModes( v8::Object::New() );
        ioObj->Set(JSTR("iomode"),ioModes);
#define M(X) SET(ioModes,#X,(JINT(WHIO_MODE_ ## X)))
        M(INVALID);
        M(UNKNOWN);
        M(READ);
        M(WRITE);
        M(RO);
        M(RW);
        M(WO);
        M(RWC);
        M(FLAG_ONLY);
        M(FLAG_CREATE);
        M(FLAG_EXCL);
        M(FLAG_TRUNCATE);
        M(FLAG_FAIL_IF_EXISTS);
        M(FLAG_APPEND);
#undef M
        JSByteArray::SetupBindings( ioObj );
        ClassCreator<whio::StreamBase>::SetupBindings(ioObj);
        ClassCreator<whio::OutStream>::SetupBindings(ioObj);
        ClassCreator<whio::InStream>::SetupBindings(ioObj);
        ClassCreator<whio::IODev>::SetupBindings(ioObj);
        ClassCreator<whio::EPFS>::SetupBindings(ioObj);
        dest->Set( JSTR(nsName), ioObj );
#undef JSTR
#undef JINT
        return;
    }

} // io namespace
} // cvv8 namespace

