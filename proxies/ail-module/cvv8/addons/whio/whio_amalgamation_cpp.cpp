/* auto-generated on Fri Aug 26 20:59:42 CEST 2011. Do not edit! */
#if !defined(_POSIX_C_SOURCE)
#define _POSIX_C_SOURCE 200112L /* needed for ftello() and friends */
#endif
#include "whio_amalgamation_cpp.hpp"
/* begin file src/whiopp.cpp */
#include <sstream>
#include <cassert>
#include <vector>

#ifndef CERR
#define CERR std::cerr << __FILE__ << ":" << std::dec << __LINE__ << ":" <<__FUNCTION__ << "(): "
#endif

namespace whio {

    Exception::Exception()
        : std::exception(),
          m_what()
    {}
    Exception::Exception( std::string const & msg )
        : std::exception(),
          m_what(msg)
    {}

    char const * Exception::what() const throw()
    {
        return m_what.c_str();
    }

    RcException::RcException( char const * funcName, int rc, std::string const & msg )
        : Exception(),
          m_rc(rc)
    {
        std::ostringstream os;
        os << funcName<<"() returned whio_rc code "<<rc
           <<" ("<<whio_rc_string(rc)<<").";
        if( !msg.empty() ) os << ' ' << msg;
        m_what = os.str();
    }

    int RcException::code() const throw()
    {
        return m_rc;
    }

    char const * RcException::codeString() const throw()
    {
        return whio_rc_string(m_rc);
    }
    
    IOBase::~IOBase()
    {
    }

    StreamBase::StreamBase()
        : m_io(NULL),
          m_ownsDevice(false)
    {
    }
    StreamBase::StreamBase(whio_stream * s, bool takeOwnership)
        : m_io(s),
          m_ownsDevice(takeOwnership)
    {
    }

    StreamBase::~StreamBase()
    {
        this->close();
    }

    void StreamBase::assertOpen() const
    {
        if( !this->m_io )
        {
            throw Exception("Stream is not opened.");
        }
    }

    void StreamBase::close() throw()
    {
        if( this->m_ownsDevice && this->m_io )
        {
            this->m_io->api->finalize( this->m_io );
        }
        this->m_io = 0;
    }

    bool StreamBase::isClosed() const
    {
        return NULL == m_io;
    }

    bool StreamBase::isGood()
    {
        return m_io
            ? m_io->api->isgood(m_io)
            : false;
    }

    whio_stream * StreamBase::takeHandle()
    {
        whio_stream * x = m_io;
        m_io = NULL;
        return x;
    }

    whio_iomode_mask StreamBase::iomode()
    {
        return ( !this->m_io )
            ? WHIO_MODE_INVALID
            : this->m_io->api->iomode(this->m_io);
    }

    InStream::InStream( whio_stream * d, bool takeOwnership )
        : StreamBase(d,takeOwnership)
    {}

    InStream::InStream( whio_dev * d, bool takeOwnership )
        : StreamBase(whio_stream_for_dev( d, takeOwnership ), true)
    {
        if( ! m_io )
        {
            throw Exception("whio_stream_for_dev() failed.");
        }
    }

    InStream::InStream( IODev & d, bool takeOwnership )
        : StreamBase(whio_stream_for_dev( d.handle(), takeOwnership ), true)
    {
        if( ! m_io )
        {
            throw Exception("whio_stream_for_dev() failed.");
        }
        if( takeOwnership ) d.takeHandle();
    }
    
    InStream::InStream()
        : StreamBase()
    {
    }
    
    InStream::~InStream() {}

    whio_size_t InStream::read( void * dest, whio_size_t n )
    {
        this->assertOpen();
        return m_io->api->read(m_io,dest,n);
    }

    OutStream::OutStream()
        : StreamBase()
    {
    }
    OutStream::OutStream( whio_stream * d, bool takeOwnership )
        : StreamBase(d,takeOwnership)
    {}

    OutStream::OutStream( whio_dev * d, bool takeOwnership )
        : StreamBase(whio_stream_for_dev( d, takeOwnership ), true)
    {
        if( ! m_io )
        {
            throw Exception("whio_stream_for_dev() failed.");
        }
    }

    OutStream::OutStream( IODev & d, bool takeOwnership )
        : StreamBase(whio_stream_for_dev( d.handle(), takeOwnership ), true)
    {
        if( ! m_io )
        {
            throw Exception("whio_stream_for_dev() failed.");
        }
        if( takeOwnership ) d.takeHandle();
    }

    
    OutStream::~OutStream()
    {
        if( this->m_io )
        {
            m_io->api->flush(m_io);
        }
    }

    whio_size_t OutStream::write( void const * src, whio_size_t n )
    {
        this->assertOpen();
        return m_io->api->write(m_io,src,n);
    }

    void OutStream::flush()
    {
        this->assertOpen();
        int const rc = this->m_io->api->flush( this->m_io );
        if( rc ) throw RcException("OutStream::flush",rc);
    }

    IODev::IODev()
        : m_io(NULL),
          m_ownsDevice(false)
    {
    }
    IODev::IODev(whio_dev *d, bool takeOwnership)
        : m_io(d),
          m_ownsDevice(takeOwnership)
    {}
    
    IODev::~IODev()
    {
        this->close();
    }

    void IODev::assertOpen() const
    {
        if( ! this->m_io )
        {
            throw Exception("Stream is not opened.");
        }
    }

    void IODev::close() throw()
    {
        if( this->m_ownsDevice && this->m_io )
        {
            this->m_io->api->finalize( this->m_io );
        }
        this->m_io = 0;
    }

    bool IODev::isClosed() const
    {
        return NULL == m_io;
    }

    whio_dev * IODev::takeHandle()
    {
        whio_dev * x = m_io;
        m_io = NULL;
        return x;
    }

    whio_iomode_mask IODev::iomode()
    {
        return ( !this->m_io )
            ? WHIO_MODE_INVALID
            : this->m_io->api->iomode(this->m_io);
    }

    void IODev::flush()
    {
        this->assertOpen();
        int const rc = this->m_io->api->flush( this->m_io );
        if( rc ) throw RcException("IODev::flush",rc);
    }
    

    whio_size_t IODev::read( void * dest, whio_size_t n )
    {
        this->assertOpen();
        return m_io->api->read(m_io,dest,n);
    }

    whio_size_t IODev::write( void const * src, whio_size_t n )
    {
        this->assertOpen();
        return m_io->api->write(m_io,src,n);
    }

    void IODev::clearError()
    {
        this->assertOpen();
        int const rc = this->m_io->api->clear_error(this->m_io);
        if( rc ) throw RcException("IODev::clearError",rc);
    }

    int IODev::error()
    {
        this->assertOpen();
        return this->m_io->api->error(this->m_io);
    }

    bool IODev::eof()
    {
        this->assertOpen();
        return 0 != this->m_io->api->eof(this->m_io);
    }
    whio_size_t IODev::tell()
    {
        this->assertOpen();
        whio_size_t const rc = this->m_io->api->tell(this->m_io);
        if( whio_rc.SizeTError == rc )
        {
            throw Exception("tell() returned whio_rc.SizeTError.");
        }
        else return rc;
    }

    whio_size_t IODev::seek( whio_off_t off, int whence )
    {
        this->assertOpen();
        whio_size_t const rc = this->m_io->api->seek(this->m_io, off, whence);
        if( whio_rc.SizeTError == rc )
        {
            throw Exception("seek() returned whio_rc.SizeTError.");
        }
        else return rc;
    }

    void IODev::truncate( whio_off_t sz )
    {
        this->assertOpen();
        int const rc = this->m_io->api->truncate(this->m_io, sz);
        if( rc ) throw RcException("IODev::truncate",rc);
    }

    whio_size_t IODev::size()
    {
        this->assertOpen();
        return whio_dev_size( m_io );
    }

    void MemoryIODev::checkInit( whio_size_t sz )
    {
        if( ! m_io )
        {
            std::ostringstream os;
            os << "Initialization of memory buffer with "
               << "(size="<<sz<<") failed.";
            throw Exception(os.str());
        }
    }

    MemoryIODev::MemoryIODev( whio_size_t size, float expFactor )
        : IODev(whio_dev_for_membuf(size, expFactor),true)
    {
        this->checkInit(size);
    }

    MemoryIODev::MemoryIODev( void * mem, whio_size_t size )
        : IODev(whio_dev_for_memmap_rw(mem, size), true)
    {
        this->checkInit(size);
    }

    MemoryIODev::MemoryIODev( void const * mem, whio_size_t size )
        : IODev(whio_dev_for_memmap_ro(mem, size), true)
    {
        this->checkInit(size);
    }

    whio_size_t MemoryIODev::bufferSize()
    {
        whio_size_t sz = 0;
        int const rc = whio_dev_ioctl( this->m_io,
                                       whio_dev_ioctl_BUFFER_size,
                                       &sz );
        if( rc )
        {
            std::ostringstream os;
            os << "Internal error: we expect "
               << "whio_dev_ioctl_BUFFER_size to succeed here.";
            throw RcException("MemoryIODev::bufferSize", rc,os.str());
        }
        return sz;
    }

    void const * MemoryIODev::buffer() const
    {
        unsigned char const * buf = NULL;
        int const rc = whio_dev_ioctl( this->m_io,
                                       whio_dev_ioctl_BUFFER_uchar_ptr,
                                       &buf );
        assert( 0 == rc );
        if( rc )
        {
            std::ostringstream os;
            os << "Internal error: we expect "
               << "whio_dev_ioctl_BUFFER_uchar_ptr to succeed here.";
            throw RcException("MemoryIODev::buffer", rc,os.str());
        }
        return buf;
    }

    
    Subdevice::Subdevice( IODev & parent, whio_size_t lowerBound, whio_size_t upperBound )
        : IODev(whio_dev_subdev_create( parent.handle(), lowerBound, upperBound ),
                true)
    {
        if( ! m_io )
        {
            std::ostringstream os;
            os << "Could not initialize subdevice of parent @"<<parent.handle()
               << " with the bounds ("<< lowerBound << ", "
               << upperBound <<").";
            throw Exception(os.str());
        }
    }

    void Subdevice::rebound( IODev & parent, whio_size_t lowerBound, whio_size_t upperBound )
    {
        int const rc = whio_dev_subdev_rebound2( m_io, parent.handle(), lowerBound, upperBound );
        if(rc)
        {
            throw RcException("Subdevice::rebound",rc,"whio_dev_subdev_rebound2() failed");
        }
    }

    void Subdevice::rebound( whio_size_t lowerBound, whio_size_t upperBound )
    {
        int const rc = whio_dev_subdev_rebound( m_io, lowerBound, upperBound );
        if(rc)
        {
            throw RcException("Subdevice::rebound",rc,"whio_dev_subdev_rebound() failed");
        }
    }


    struct StdOStreamBuf::Impl
    {
	std::ostream & in;
	whio_stream * out;
	std::streambuf * oldBuf;
        bool ownsWh;
        typedef std::vector<std::istream::char_type> BufferType;
        BufferType buf;
        uint32_t bufSize;
        uint32_t pos;
	Impl(std::ostream & i, whio_stream * o, bool ownsWh,
             uint32_t bufSize ) :
	    in(i),
	    out(o),
	    oldBuf(i.rdbuf()),
            ownsWh(ownsWh),
            buf(bufSize,0),
            bufSize(bufSize),
            pos(0)
	{
	    if( !o )// || (!(WHIO_MODE_WRITE & o->api->iomode(o))) )
	    {
		throw RcException("StdOStreamBuf::StdOStreamBuf",
                                  whio_rc.ArgError,
                                  "StdOStreamBuf::StdOStreamBuf() requires that the whio_stream be open in write mode.");
	    }
	}
	~Impl()
	{
            if(ownsWh && this->out)
            {
                this->out->api->finalize(this->out);
            }
	}
    };


    StdOStreamBuf::StdOStreamBuf( std::ostream & in,
                                  whio_stream * out,
                                  bool ownsWh,
                                  uint32_t bufSize)
	: impl(new Impl(in,out,ownsWh,bufSize))
    {
#if 0
        if(bufSize)
        {
            char * pp = &impl->buf[0];
            this->setp(pp,pp + bufSize);
        }
#endif
	this->setg(0,0,0);
	in.rdbuf( this );
    }

    StdOStreamBuf::~StdOStreamBuf()
    {
        if( impl->pos ) this->sync();
	std::streambuf * rb = impl->in.rdbuf();
	if( rb == this )
	{
	    impl->in.rdbuf( impl->oldBuf );
	}
	delete impl;
    }

    int StdOStreamBuf::overflow(int c)
    {
	typedef traits_type CT;
	if( CT::eq_int_type(c, CT::eof())) return CT::eof();
        else if( !impl->bufSize )
        { // non-buffering impl
            if (!CT::eq_int_type(c, CT::eof()))
            {
                char x = static_cast<CT::char_type>(c);
                return (1 == impl->out->api->write( impl->out, &x, 1 ))
                    ? CT::not_eof(c)
                    : CT::eof();
            }
            else return CT::eof();
        }
        else
        { // buffering impl
            assert( impl->pos <= impl->bufSize );
            if( impl->pos == impl->bufSize )
            {
                if( this->sync()) return CT::eof();
            }
            return CT::not_eof( impl->buf[impl->pos++] = (char)c );
        }
    }

    int StdOStreamBuf::sync()
    {
        whio_size_t const sz = impl->pos;
        impl->pos = 0;
        return !sz
            ? 0
            : ((sz == impl->out->api->write( impl->out,
                                             &impl->buf[0], sz ))
               ? 0
               : -1)
            ;
    }

    struct StdIStreamBuf::Impl
    {
	std::istream & sstr;
	whio_stream * wstr;
	std::streambuf * oldBuf;
        bool ownsWh;
        typedef std::vector<std::istream::char_type> BufferType;
        BufferType buf;
	Impl(std::istream & i, whio_stream * o,
             bool ownsWh, uint32_t bufSize ) :
	    sstr(i),
	    wstr(o),
	    oldBuf(i.rdbuf()),
            ownsWh(ownsWh),
	    buf(bufSize,0)
	{
            if( !bufSize )
            {
		throw RcException("StdIStreamBuf::StdIStreamBuf",
                                  whio_rc.ArgError,
                                  "Buffer size may not be 0.");
            }
	    if( !o || !(WHIO_MODE_READ & o->api->iomode(o)) )
	    {
		throw RcException("StdIStreamBuf::StdIStreamBuf",
                                  whio_rc.ArgError,
                                  "StdIStreamBuf::StdIStreamBuf() requires that the whio_stream be open in read mode.");
	    }
	}
	~Impl()
	{
            if( this->ownsWh && this->wstr )
            {
                this->wstr->api->finalize( this->wstr );
            }
	}
    };


    StdIStreamBuf::StdIStreamBuf( std::istream & in,
                                  whio_stream * out,
                                  bool ownsWh,
                                  uint32_t bufSize)
	: impl(new Impl(in,out,ownsWh,bufSize))
    {
	this->setp(0,0);
	this->setg(0,0,0);
	in.rdbuf( this );
    }

    StdIStreamBuf::~StdIStreamBuf()
    {
	std::streambuf * rb = impl->sstr.rdbuf();
	if( rb == this )
	{
	    impl->sstr.rdbuf( impl->oldBuf );
	}
	delete impl;
    }

    int StdIStreamBuf::underflow()
    {
	std::istream::char_type * dest = &impl->buf[0];
	whio_size_t rd = impl->wstr->api->read( impl->wstr, dest, impl->buf.size() );
	if( rd < 1 )
	{
	    return traits_type::eof();
	}
	this->setg(dest,dest,dest+rd);
	return traits_type::not_eof(*dest);
    }


    StdOStream::StdOStream( whio_stream * proxy, bool ownsWh, uint32_t bufferSize )
	: m_buf( *this, proxy, ownsWh, bufferSize )
    {
    }
    StdOStream::~StdOStream()
    {
    }

    StdOStream::StdOStream( OutStream & d, bool takeOwnership, uint32_t bufferSize )
        : m_buf( *this, d.handle(), takeOwnership, bufferSize )
    {
        if( takeOwnership ) d.takeHandle();
    }

    StdOStream::StdOStream( IODev & d, bool takeOwnership, uint32_t bufferSize )
        : m_buf( *this,
                 whio_stream_for_dev( d.handle(), takeOwnership),
                 true, bufferSize)
    {
        if( takeOwnership ) d.takeHandle();
    }

    StdIStream::StdIStream( whio_stream * proxy, bool ownsWh, uint32_t bufferSize )
	: m_buf( *this, proxy, ownsWh, bufferSize )
    {
    }

    StdIStream::StdIStream( InStream & d, bool takeOwnership, uint32_t bufferSize )
        : m_buf( *this, d.handle(), takeOwnership, bufferSize )
    {
        if( takeOwnership ) d.takeHandle();
    }

    StdIStream::StdIStream( IODev & d, bool takeOwnership, uint32_t bufferSize )
        : m_buf( *this,
                 whio_stream_for_dev( d.handle(), takeOwnership),
                 true, bufferSize)
    {
        if( takeOwnership ) d.takeHandle();
    }

    
    StdIStream::~StdIStream()
    {
    }

}

#undef CERR
/* end file src/whiopp.cpp */
/* begin file src/whiopp_file.cpp */
#if defined(__cplusplus)
#include <sstream>

namespace whio {
    FileInStream::FileInStream( char const * fname )
        : InStream( fname ? whio_stream_for_filename( fname, "r" ) : NULL, true )
    {
        if( ! m_io )
        {
            std::ostringstream os;
            os << "Opening of file ["<<fname<<"] for reading failed.";
            throw Exception(os.str());
        }
    }

    FileInStream::FileInStream( FILE * f, bool takeHandle )
        : InStream(f ? whio_stream_for_FILE( f, takeHandle ) : NULL, true)
    {
        if( ! m_io )
        {
            std::ostringstream os;
            os << "Could not proxy FILE handle @"<<(void const *)f<<'.';
            throw Exception(os.str());
        }
    }

    FileInStream::FileInStream( int fno )
        : InStream(whio_stream_for_fileno( fno, false ), true)
    {
        if( ! m_io )
        {
            std::ostringstream os;
            os << "Could not proxy file handle @"<<fno<<'.';
            throw Exception(os.str());
        }
    }

    FileOutStream::FileOutStream( char const * fname, bool trunc )
        : OutStream((whio_stream*)NULL,true)
    {
        char const * mode = trunc ? "wb" : "ab";
        this->m_io = fname ? whio_stream_for_filename( fname, mode ) : NULL;
        if( ! m_io )
        {
            std::ostringstream os;
            os << "Opening of file ["<<fname<<"] with mode ["<<mode<<"] "
               << "failed.";
            throw Exception(os.str());
        }
    }

    FileOutStream::FileOutStream( FILE * f, bool takeHandle )
        : OutStream(f ? whio_stream_for_FILE( f, takeHandle ) : NULL, true)
    {
        if( ! m_io )
        {
            std::ostringstream os;
            os << "Could not proxy FILE handle @"<<(void const *)f<<'.';
            throw Exception(os.str());
        }
    }

    FileOutStream::FileOutStream( int fno )
        : OutStream(whio_stream_for_fileno( fno, true ), true)
    {
        if( ! m_io )
        {
            std::ostringstream os;
            os << "Could not proxy file handle @"<<fno<<'.';
            throw Exception(os.str());
        }
    }

    FileIODev::FileIODev( char const * fname, char const * mode )
        : IODev((fname && mode) ? whio_dev_for_filename( fname, mode ) : NULL, true)
    {
        if( ! m_io )
        {
            std::ostringstream os;
            os << "Opening of file ["<<fname<<"] with mode ["<<mode<<"] "
               << "failed.";
            throw Exception(os.str());
        }
    }

    FileIODev::FileIODev( char const * fname, whio_iomode_mask flags, short perms )
        : IODev(NULL,true)
    {
        int const rc = whio_dev_posix_open2( &this->m_io, fname, flags, perms );
        if( rc )
        {
            std::ostringstream os;
            os << "Open failed for file ["<<fname<<"] "
               << "with code "<<rc<<" ("<<whio_rc_string(rc)<<") "
               << "with iomode flags ["<<std::hex<<flags<<"] and "
               << "permissions [" <<std::oct << perms << "].";
            throw Exception(os.str());
        }
    }

    FileIODev::FileIODev( FILE * f, bool takeHandle )
        : IODev(f ? whio_dev_for_FILE( f, takeHandle ) : NULL,true)
    {
        if( ! m_io )
        {
            std::ostringstream os;
            os << "Could not proxy FILE handle @"<<(void const *)f<<'.';
            throw Exception(os.str());
        }
    }

    FileIODev::FileIODev( int fno, char const * mode )
        : IODev(whio_dev_for_fileno( fno, mode ),true)
    {
        if( ! m_io )
        {
            std::ostringstream os;
            os << "Could not proxy file handle @"<<fno<<'.';
            throw Exception(os.str());
        }
    }

    
}
#endif
/* C++ include guard */
/* end file src/whiopp_file.cpp */
/* begin file src/whiopp_util.cpp */
#if defined(__cplusplus)
#include <sstream>
#include <cassert>

namespace whio {

#define HT_TYPE_NAME(T) char const * HTKeyTypeName< T >::Name = #T"*"
    HT_TYPE_NAME(int8_t);
    HT_TYPE_NAME(uint8_t);
    HT_TYPE_NAME(int16_t);
    HT_TYPE_NAME(uint16_t);
    HT_TYPE_NAME(int32_t);
    HT_TYPE_NAME(uint32_t);
    HT_TYPE_NAME(int64_t);
    HT_TYPE_NAME(uint64_t);
#undef HT_TYPE_NAME
    
    HashTable::FormatOpt::FormatOpt()
        : hashSize(whio_ht_opt_empty.hashSize),
          mutex(whio_ht_opt_empty.mutex),
          functionSet("string")
    {
    }


    HashTable::Record::Record()
        : m_ht(NULL),
          m_rec(whio_ht_record_empty)
    {}

    bool HashTable::Record::isEmpty() const
    {
        return (NULL==m_ht) || (0 == m_rec.keyLen);
    }
    
    void HashTable::Record::assign( HashTable *h, whio_ht_record const & rec )
    {
        m_ht = h;
        m_rec = rec;
    }

#if 0
    whio_ht_record * HashTable::Record::handle()
    {
        return &m_rec;
    }
#endif

    whio_ht_record const * HashTable::Record::handle() const
    {
        return &m_rec;
    }

    void HashTable::Record::remove()
    {
        /* reminder: this is not technically safe vis-a-vis ht's
           mutex.  Maybe we should lock for each record? But that
           would impose a recursive locks requirement. Hmm.
        */
        int const rc = whio_ht_record_remove( &m_ht->m_ht, &m_rec );
        if( rc ) throw RcException("whio_ht_record_remove",rc);
    }

    whio_size_t HashTable::Record::keyLength() const
    {
        return whio_ht_key_len( &m_rec );
    }

    whio_size_t HashTable::Record::valueLength() const
    {
        return whio_ht_value_len( &m_rec );
    }

    
    HashTable::HashTable()
        : m_ht(whio_ht_empty)
    {}

    HashTable::HashTable( whio_dev * dev, HashTable::FormatOpt const & opt )
        : m_ht(whio_ht_empty)
    {
        format( *this, dev, opt );
    }

    HashTable::HashTable( IODev & dev, HashTable::FormatOpt const & opt )
        : m_ht(whio_ht_empty)
    {
        format( *this, dev, opt );
    }
    HashTable::HashTable( whio_dev * dev )
        : m_ht(whio_ht_empty)
    {
        open( *this, dev );
    }
    HashTable::HashTable( IODev & dev )
        : m_ht(whio_ht_empty)
    {
        open( *this, dev );
    }
    
    HashTable::~HashTable()
    {
        this->close();
    }

    whio_ht * HashTable::handle()
    {
        return &m_ht;
    }

    whio_ht const * HashTable::handle() const
    {
        return &m_ht;
    }

    void HashTable::assertOpen() const
    {
        if( ! m_ht.devs.ht )
        {
            throw Exception("HashTable storage has been closed.");
        }
    }

    void HashTable::close()
    {
        if( m_ht.devs.ht )
        {
            whio_ht_close( &m_ht );
        }
    }

    static void convertFormatOpt( HashTable::FormatOpt const & opt,
                                  whio_ht_opt * tgt )
    {
        *tgt = whio_ht_opt_empty;
        tgt->hashSize = opt.hashSize;
        tgt->mutex = opt.mutex;

    }


    void HashTable::format( HashTable & self, whio_dev * dev, HashTable::FormatOpt const & opt)
    {
        whio_ht_opt fsopt;
        convertFormatOpt( opt, &fsopt );
        whio_ht * HT = &self.m_ht;
        int rc = whio_ht_format( &HT, dev, &fsopt, opt.functionSet );
        if( rc )
        {
            std::ostringstream os;
            os << "functionSet=["<<opt.functionSet<<']';
            throw RcException("whio_ht_format", rc, os.str() );
        }
    }

    HashTable * HashTable::format( whio_dev * dev, HashTable::FormatOpt const & opt)
    {
        return new HashTable(dev, opt);
    }

    void HashTable::format( HashTable & self,
                            IODev & dev,
                            HashTable::FormatOpt const & opt )
    {
        format( self, dev.handle(), opt );
        whio_dev * d; d = dev.takeHandle();
        assert( d == self.m_ht.vlbm.dev );
    }

    HashTable * HashTable::format( IODev & dev,
                                   HashTable::FormatOpt const & opt )
    {
        return new HashTable(dev, opt);
    }

    void HashTable::open( HashTable & self, whio_dev * dev )
    {
        whio_ht * HT = &self.m_ht;
        int const rc = whio_ht_open( &HT, dev );
        if( rc )
        {
            throw RcException("whio_ht_open", rc );
        }
    }

    HashTable * HashTable::open( whio_dev * dev )
    {
        return new HashTable(dev);
    }

    void HashTable::open( HashTable & self, IODev & dev )
    {
        open( self, dev.handle() );
        assert( dev.handle() == self.m_ht.vlbm.dev );
        dev.takeHandle();
    }

    HashTable * HashTable::open( IODev & dev )
    {
        return new HashTable(dev);
    }

    whio_size_t HashTable::size()
    {
        this->assertOpen();
        whio_size_t const sz = whio_dev_size( m_ht.vlbm.dev );
        return (whio_rc.SizeTError == sz)
            ? 0
            : sz;
    }

    bool HashTable::isClosed() const
    {
        return !whio_ht_is_open(&m_ht);
    }

    bool HashTable::contains(void const * key, whio_size_t keyLen)
    {
        this->assertOpen();
        return whio_ht_contains( &m_ht, key, keyLen );
    }
    void HashTable::insert( void const * key, whio_size_t keyLen,
                            void const * value, whio_size_t valueLen )
    {
        this->assertOpen();
        int const rc = whio_ht_insert( &m_ht, key, keyLen, value, valueLen );
        if( rc ) throw RcException("whio_ht_insert",rc);
    }

    bool HashTable::remove( void const * key, whio_size_t keyLen )
    {

        this->assertOpen();
        int const rc = whio_ht_remove( &m_ht, key, keyLen );
        if( 0 == rc ) return true;
        else if( whio_rc.NotFoundError == rc ) return false;
        else throw RcException("whio_ht_remove",rc);
        return false /* cannot be reached */;
    }

    bool HashTable::search( void const * key, whio_size_t keyLen, HashTable::Record & tgt )
    {
        whio_ht_record rec = whio_ht_record_empty;
        int const rc = whio_ht_search( &m_ht, key, keyLen, &rec );
        if( whio_rc.NotFoundError == rc ) return false;
        else if( !rc )
        {
            tgt.assign(this, rec);
            return true;
        }
        else throw RcException("whio_ht_search",rc);
        return false /* cannot be reached */;
    }

    void HashTable::wipeOnRemove( bool b )
    {
        this->assertOpen();
        whio_ht_opt_set_wipe_on_remove(&m_ht, b)
            /* this can only fail if m_ht is NULL (which of course it
              never is).*/
            ;
    }
    
}

#endif
/* C++ include guard */
/* end file src/whiopp_util.cpp */
/* begin file pfs/whiopp_epfs.cpp */
#if defined(__cplusplus)

#include <cassert>
#include <sstream>
#include <iostream>
#include <cstring> /* strlen() */
#ifndef CERR
#define CERR std::cerr << __FILE__ << ":" << std::dec << __LINE__ << ":" <<__FUNCTION__ << "(): "
#endif

namespace whio {

    EPFS::PseudoFile::PseudoFile(EPFS & fs, whio_dev *d)
        : IODev(d,true),
          m_fs(fs)
    {
    }

    EPFS::PseudoFile::~PseudoFile()
    {
    }

    whio_epfs_id_t EPFS::PseudoFile::inodeId() const
    {
        this->assertOpen();
        return whio_epfs_dev_inode_id( m_io );
    }

    whio_epfs_inode const * EPFS::PseudoFile::inode() const
    {
        this->assertOpen();
        return whio_epfs_dev_inode_c( m_io );
    }

    void EPFS::PseudoFile::touch( uint32_t time )
    {
        int const rc = whio_epfs_dev_touch( m_io, time );
        if(rc) throw RcException( "whio_epfs_dev_touch", rc );
    }

    uint32_t EPFS::PseudoFile::mtime() const
    {
        uint32_t val = 0;
        int const rc = whio_epfs_dev_mtime( m_io, &val );
        if(rc) throw RcException( "whio_epfs_dev_mtime", rc );
        return val;
    }

    void EPFS::PseudoFile::clientFlags( uint32_t val )
    {
        int const rc = whio_epfs_dev_client_flags_set( m_io, val );
        if( rc ) throw RcException("whio_epfs_dev_client_flags_set",rc);
    }

    uint32_t EPFS::PseudoFile::clientFlags() const
    {
        uint32_t val = 0;
        int const rc = whio_epfs_dev_client_flags_get( m_io, &val );
        if(rc) throw RcException( "whio_epfs_dev_client_flags_get", rc );
        return val;
    }

    void EPFS::PseudoFile::name( char const * name )
    {
        this->m_fs.name( this->inodeId(), name );
    }

    std::string EPFS::PseudoFile::name()
    {
        return this->m_fs.name( this->inodeId() );
    }

    bool EPFS::PseudoFile::isInternal() const
    {
        return whio_epfs_inode_is_internal( this->inode() );
    }
    
    whio_epfs_fsopt const * EPFS::defaultFsOpt()
    {
        static whio_epfs_fsopt o = whio_epfs_fsopt_empty;
        if( !o.inodeCount )
        {
            o.maxBlocks = 0;
            o.blockSize = 1024 * 16;
            o.inodeCount = 128;
        }
        return &o;
    }
    EPFS::EPFS()
        : m_fs(whio_epfs_empty)
    {
    }

    EPFS::EPFS( whio_dev * dev, bool takeStore, whio_epfs_fsopt const * opt )
        : m_fs(whio_epfs_empty)
    {
        mkfs( *this, dev, takeStore, opt );
    }

    EPFS::EPFS( char const * filename, bool allowOverwrite, whio_epfs_fsopt const * fsopt )
        : m_fs(whio_epfs_empty)
    {
        mkfs( *this, filename, allowOverwrite, fsopt );
    }

    EPFS::EPFS( char const * filename, bool writeMode )
        : m_fs(whio_epfs_empty)
    {
        openfs( *this, filename, writeMode );
    }

    EPFS::EPFS( whio_dev * store, bool takeStore )
        : m_fs(whio_epfs_empty)
    {
        openfs( *this, store, takeStore );
    }

    void EPFS::assertOpen() const
    {
        if( !this->m_fs.dev )
        {
            throw Exception("EPFS is not opened.");
        }
    }
    
    EPFS::~EPFS()
    {
        this->close();
    }
    whio_epfs * EPFS::handle()
    {
        return &m_fs;
    }
    whio_epfs const * EPFS::handle() const
    {
        return &m_fs;
    }

    void EPFS::close() throw()
    {
        if( m_fs.dev )
        {
            whio_epfs_close(&m_fs);
            assert( NULL == m_fs.dev );
        }
    }

    bool EPFS::isClosed() const
    {
        return NULL == m_fs.dev;
    }

    void EPFS::flush()
    {
        this->assertOpen();
        int const rc = whio_epfs_flush( &m_fs );
        if( rc ) throw RcException("whio_epfs_flush",rc);
    }

    whio_epfs_id_t EPFS::currentBlockCount() const
    {
        this->assertOpen();
        return whio_epfs_block_count(&m_fs);
    }

    whio_epfs_fsopt const * EPFS::fsopt() const
    {
        return whio_epfs_options(&m_fs);
    }
    
    void EPFS::mkfs( EPFS & fs, whio_dev * d, bool takeStore, whio_epfs_fsopt const * opt )
    {
        whio_epfs * FS = &fs.m_fs;
        if( ! opt ) opt = EPFS::defaultFsOpt();
        int rc = whio_epfs_mkfs2( &FS, d, opt, takeStore );
        if( rc )
        {
            assert( NULL == fs.m_fs.dev );
            throw RcException("whio_epfs_mkfs2", rc);
        }
    }

    EPFS * EPFS::mkfs( whio_dev * d, bool takeStore, whio_epfs_fsopt const * opt )
    {
        EPFS * fs = new EPFS();
        try
        {
            mkfs( *fs, d, takeStore, opt );
            return fs;
        }
        catch(...)
        {
            delete fs;
            throw;
        }
    }

    void EPFS::mkfs( EPFS & fs,
                     char const * filename,
                     bool allowOverwrite,
                     whio_epfs_fsopt const * opt )
    {
        whio_epfs * FS = &fs.m_fs;
        if( ! opt ) opt = defaultFsOpt();
        int rc = whio_epfs_mkfs_file( &FS, filename, allowOverwrite, opt );
        if( rc )
        {
            throw RcException("whio_epfs_mkfs", rc);
        }
    }

    EPFS * EPFS::mkfs( char const * filename,
                       bool allowOverwrite,
                       whio_epfs_fsopt const * opt )
    {
        EPFS * fs = new EPFS();
        try
        {
            mkfs( *fs, filename, allowOverwrite, opt );
            return fs;
        }
        catch(...)
        {
            delete fs;
            throw;
        }
    }

    void EPFS::installNamer( char const * impl )
    {
        this->assertOpen();
        whio_epfs_namer_reg reg = whio_epfs_namer_reg_empty;
        int rc = whio_epfs_namer_reg_search( impl, &reg );
        if( rc ) throw RcException("whio_epfs_namer_reg_search",rc);
        rc = whio_epfs_namer_format( &m_fs, &reg );
        if( rc ) throw RcException("whio_epfs_namer_format",rc);
    }
    
    void EPFS::openfs( EPFS & fs, whio_dev * dev, bool takeStore )
    {
        whio_epfs * FS = &fs.m_fs;
        int rc = whio_epfs_openfs2( &FS, dev, takeStore );
        if( rc )
        {
            throw RcException("whio_epfs_openfs2", rc);
        }
    }

    EPFS * EPFS::openfs( whio_dev * dev, bool takeStore )
    {
        EPFS * fs = new EPFS();
        try
        {
            openfs( *fs, dev, takeStore );
            return fs;
        }
        catch(...)
        {
            delete fs;
            throw;
        }
    }

    void EPFS::openfs( EPFS & fs, char const * filename, bool writeMode )
    {
        whio_epfs * FS = &fs.m_fs;
        int rc = whio_epfs_openfs_file( &FS, filename, writeMode );
        if( rc )
        {
            throw RcException("whio_epfs_openfs_file", rc);
        }
    }

    EPFS * EPFS::openfs( char const * filename, bool writeMode )
    {
        EPFS * fs = new EPFS();
        try
        {
            openfs( *fs, filename, writeMode );
            return fs;
        }
        catch(...)
        {
            delete fs;
            throw;
        }
    }


    bool EPFS::isRW() const
    {
        this->assertOpen();
        return whio_epfs_is_rw( &this->m_fs );
    }

    EPFS::PseudoFile * EPFS::openById( whio_epfs_id_t inodeID, whio_iomode_mask mode )
    {
        this->assertOpen();
        whio_dev * dev = NULL;
        int rc = whio_epfs_dev_open( &this->m_fs, &dev, inodeID, mode );
        if( rc )
        {
            assert( NULL == dev );
            std::ostringstream os;
            os << "whio_epfs_dev_open("<<inodeID<<", "
               << "0x" << std::hex<<mode<<") failed with "
               << "code " <<std::dec << rc
               << " ("<<whio_rc_string(rc)<<").\n";
            throw Exception(os.str());
        }
        return new EPFS::PseudoFile(*this, dev);
    }

    EPFS::PseudoFile * EPFS::openByName( char const * name, whio_iomode_mask mode )
    {
        this->assertOpen();
        if( ! name || !*name ) throw Exception("Filename parameter may not be NULL or empty.");
        whio_dev * dev = NULL;
        uint32_t const nlen = std::strlen(name);
        int rc = whio_epfs_dev_open_by_name( &this->m_fs, &dev, name, nlen, mode );
        if( rc )
        {
            assert( NULL == dev );
            std::ostringstream os;
            os << "file=["<<name<<"], iomode=["
               << "0x" << std::hex<<mode<<"]";
            std::string const & str(os.str());
            throw RcException("whio_epfs_dev_open_by_name", rc , str.c_str());
        }
        return new EPFS::PseudoFile(*this, dev);
    }

    void EPFS::unlink( whio_epfs_id_t inodeID )
    {
        this->assertOpen();
        int const rc = whio_epfs_unlink( &m_fs, inodeID );
        if( rc ) throw RcException("whio_epfs_unlink", rc );
    }
    
    void EPFS::unlink( char const * name )
    {
        this->assertOpen();
        int const rc = whio_epfs_unlink_by_name( &m_fs,
                                                 name,
                                                 name ? strlen(name) : 0 );
        if( rc )
        {
            std::ostringstream os;
            os << "name=["<<name<<"]";
            throw RcException("whio_epfs_unlink_by_name", rc, os.str() );
        }
        
    }

    void EPFS::label( char const * name )
    {
        this->assertOpen();
        int const rc = whio_epfs_label_set( &m_fs, name, name ? strlen(name) : 0 );
        if( rc ) throw RcException("whio_epfs_label_set", rc );
    }

    std::string EPFS::label()
    {
        this->assertOpen();
        char buf[whio_epfs_sizeof_label_payload+1];
        std::memset( buf, 0, sizeof(buf)/sizeof(buf[0]) );
        int const rc = whio_epfs_label_get( &m_fs, buf );
        if( rc ) throw RcException("whio_epfs_label_get", rc);
        return std::string(buf);
    }

    bool EPFS::hasNamer() const
    {
        this->assertOpen();
        return whio_epfs_has_namer( &m_fs );
    }
    
    void EPFS::name( whio_epfs_id_t inodeID, char const * name )
    {
        this->assertOpen();
        int const rc = whio_epfs_name_set( &m_fs, inodeID, name, name ? strlen(name) : 0 );
        if( rc )
        {
            std::ostringstream os;
            os << "inodeID="<<inodeID<<", name=["<<name<<"]";
            throw RcException( "whio_epfs_name_set", rc, os.str() );
        }
    }

    std::string EPFS::name( whio_epfs_id_t inodeID )
    {
        this->assertOpen();
        enum { NameBufSize = 2048 };
        char buf[NameBufSize] = {0};
        std::memset( buf, 0, sizeof(buf)/sizeof(buf[0]) );
        whio_size_t nlen = NameBufSize-1/*for trailing NULL, which is not currently guaranteed by name_get()!*/;
        int const rc = whio_epfs_name_get( &m_fs, inodeID, buf, &nlen );
        if( rc )
        {
            std::ostringstream os;
            os << "inodeID="<<inodeID;
            throw RcException("whio_epfs_name_get", rc, os.str() );
        }
        else if( nlen >= NameBufSize )
        {
            assert( 0 && "whio_epfs_name_get() SHOULD have failed but did not." );
            throw std::range_error("Buffer overflow, possible stack corruption, due to extremely "
                                   "long name in EFS. "
                                   "whio_epfs_name_get() SHOULD have failed but did not.");
        }
        return std::string(buf, nlen);
    }

    whio_epfs_id_t EPFS::inodeId( char const * name )
    {
        this->assertOpen();
        whio_epfs_id_t val = 0;
        int const rc = whio_epfs_name_search( &m_fs, &val, name, name ? strlen(name) : 0 );
        if( rc && (whio_rc.NotFoundError != rc)) throw RcException("whio_epfs_name_search",rc);
        else return val;
    }

    whio_size_t EPFS::size()
    {
        this->assertOpen();
        return whio_dev_size( m_fs.dev );
    }
    
}

#undef CERR
#endif
/* C++ include guard */
/* end file pfs/whiopp_epfs.cpp */
