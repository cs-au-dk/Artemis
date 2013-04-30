/* auto-generated on Fri Aug 26 20:59:42 CEST 2011. Do not edit! */
#if !defined(_POSIX_C_SOURCE)
#define _POSIX_C_SOURCE 200112L /* needed for ftello() and friends */
#endif
#include "whio_amalgamation.h"
/* begin file include/wh/whio/whiopp.hpp */
#if !defined(WANDERINGHORSE_NET_WHIOPP_HPP_INCLUDED)
#define WANDERINGHORSE_NET_WHIOPP_HPP_INCLUDED
#include <stdexcept>
#include <iostream>

/** @namespace whio

   The whio namespace houses C++ wrappers for various whio C APIs.
*/
namespace whio {

    using ::whio_iomode_mask;
    using ::whio_iomodes;

    class Exception : public std::exception
    {
    protected:
        std::string m_what;
        Exception();
    public:
        virtual ~Exception() throw() {}
        Exception( std::string const & msg );
        virtual char const * what() const throw();
    };
    /**
       Exception type specifically for reporting whio_rc error codes.
    */
    class RcException : public Exception
    {
    private:
        int m_rc;
    public:
        virtual ~RcException() throw() {}

        /**
           funcName should be the name of the whio routine which
           failed and rc should be its error code (IF that error code
           is one of the whio_rc values, else the generated error
           message will be wrong!). An error string will be built out
           of that information. If msg is not empty then it is
           appended to the error string.
        */
        RcException( char const * funcName, int rc, std::string const & msg = std::string() );
        
        /**
           Returns the whio_rc error code passed to the constructor.
         */
        int code() const throw();

        /**
           Equivalent to whio_rc_string(this->code()).
        */
        char const * codeString() const throw();
    };
    

    /**
       The base-most ancestor of the IODev and Stream classes.
    */
    class IOBase
    {
    private:
        //! Not implemented.
        IOBase( const IOBase & );
        //! Not implemented.
        IOBase & operator=(IOBase const &);
    protected:
        IOBase() {}
    public:
        /**
           Subclasses which re-implemente close() must call their
           close() from their own destructors. Do not rely on a parent
           dtor to call a more-derived close(), as the virtual type
           information is lost on the way down the dtor stack.
         */
        virtual ~IOBase() = 0;

        /**
           Must close the underlying handle and free any
           resources, but must not call (delete this).
           After calling this, calling any other members
           induced undefined behaviour. Implementations
           are encouraged to throw exceptions rather than
           dereference stall/NULL pointers.
        */
        virtual void close() = 0;

        /**
           Must return the i/o mode mask.

           See whio_dev_api::iomode() and whio_stream_api::iomode()
           for the semantics.
        */
        virtual whio_iomode_mask iomode() /*FIXME in whio: const*/ = 0;
    };

    /**
       The base C++ interface wrapper for the whio_stream class.
       Clients typically use the InStream and OutStream interfaces
       intead of this base interface.
    */
    class StreamBase : public IOBase
    {
    private:
        //! Not implemented.
        StreamBase( const StreamBase & );
        //! Not implemented.
        StreamBase & operator=(StreamBase const &);
    protected:
        //! The underlying stream handle. Be Careful with this!
        whio_stream * m_io;
        //! If true then this object assumes owneship of m_io.
        bool m_ownsDevice;
        /**
           Throws if !this->m_io.

           May be overridden to check other logic.
         */
        virtual void assertOpen() const;
        StreamBase();
        /**
           Sets m_io and m_ownsDevice to the given arguments.
           Does no validation of the parameters.
         */
        StreamBase(whio_stream * s, bool takeOwnership);
    public:
        /**
           Calls close().
        */
        virtual ~StreamBase();
        /**
           If this object owns its stream then this destroys that
           stream, else it simply disowns the device.

           Deleting this object implicitly closes it.

           Subclasser notes: if the internal handle is not NULL, this
           function finalizes (if it owns it) it and then sets the
           internal handle to NULL. So after this all interaction with
           the handle is illegal.
        */
        virtual void close() throw();
        /**
           Returns true if this stream has been close()d.
        */
        bool isClosed() const;
        /**
           Returns the stream's i/o mode mask.
        */
        virtual whio_iomode_mask iomode();
        /**
           Returns true if this stream is in a "good" state.
         */
        bool isGood();
        /**
           Returns the low-level whio_stream handle. Ownership is not
           transfered by this call and clients MUST NOT destroy the
           object or transfer ownership of it elsewhere.
        */
        whio_stream * handle() { return m_io; }
        /**
           Const-correct overload.
        */
        whio_stream const * handle() const { return m_io; }

        /**
           Transfers ownership of the handle() object to the
           caller. The effect on this object is as if close()
           had been called, except that the handle is not
           closed before returning to the caller.
        */
        whio_stream * takeHandle();
    };

    /**
       The base C++ interface wrapper for the whio_dev class.

       This implementation acts as a wrapper around a raw whio_dev
       object, optionally taking ownership of the device. Subclasses
       may add type-specific APIs to the interface, but most
       subclasses are simply a collection of ctors which mirror
       specific whio_dev factory functions.
    */
    class IODev : public IOBase
    {
    protected:
        //! The underlying i/o handle. Be Careful with this!
        whio_dev * m_io;
        //! If true then this object assumes owneship of m_io.
        bool m_ownsDevice;
        /**
           Throws if !this->m_io.
         */
        void assertOpen() const;
        IODev();
    public:
        /**
           Proxies the given whio_dev object. If takeOwnership is true
           then ownership of dev is transfered to this object and dev
           will be destroyed when this object is close()d. If
           takeOwnership is false, ownership is not transfered and dev
           must outlive this object.

           Throws on error.
         */
        IODev(whio_dev *, bool takeOwnership);

        /**
           Calls close().
        */
        virtual ~IODev();

        /**
           Returns the stream's i/o mode mask.
        */
        whio_iomode_mask iomode() /*FIXME in whio: const*/;

        /**
           If this object owns its device then this destroys that
           device, else it simply disowns the device.

           Deleting this object implicitly closes it.

           Subclasser notes: if the internal handle is not NULL, this
           function finalizes (if it owns it) it and then sets the
           internal handle to NULL. So after this all interaction with
           the handle is illegal.
        */
        void close() throw();

        /**
           Returns true if this device has been close()d.
        */
        bool isClosed() const;

        /**
           See whio_dev_api::flush().

           Throws on error.
        */
        void flush();

        /**
           See whio_dev_api::read().
        */
        whio_size_t read( void * dest, whio_size_t n );

        /**
           See whio_dev_api::write().
        */
        whio_size_t write( void const * src, whio_size_t n );

        /**
           See whio_dev_api::error().
        */
        int error();

        /**
           See whio_dev_api::clearError().

           Throws on error, though that is arguable
           for this case.
        */
        void clearError();

        /**
           See whio_dev_api::eof().
        */
        bool eof();

        /**
           See whio_dev_api::tell().

           Throws if the underlying implementation
           returns whio_rc.SizeTError.
        */
        whio_size_t tell();

        /**
           See whio_dev_api::seek().

           Throws if the underlying implementation
           returns whio_rc.SizeTError.
        */
        whio_size_t seek( whio_off_t off, int whence );

        /**
           See whio_dev_api::truncate().

           Throws on error.
        */
        void truncate( whio_off_t sz );

        /**
           Returns the low-level whio_dev handle. Ownership is not
           transfered by this call and clients MUST NOT destroy the
           object or transfer ownership of it elsewhere.

           Returns NULL if this object has already been closed or had
           its handle taken away.
        */
        whio_dev * handle() { return m_io; }

        /**
           Const-correct overload.
        */
        whio_dev const * handle() const { return m_io; }

        /**
           Transfers ownership of the handle() object to the
           caller. The effect on this object is as if close()
           had been called, except that the handle is not
           closed before returning to the caller.

           Returns NULL if this object has already been closed or had
           its handle taken away.
        */
        whio_dev * takeHandle();

        /**
           Returns the device's current size. See whio_dev_size().
        */
        virtual whio_size_t size();
    };


    /**
       The base C++ interface for input whio_stream objects.

       This implementation acts as a wrapper around a raw whio_stream
       object, optionally taking ownership of the stream. Subclasses
       may add type-specific APIs to the interface, but most
       subclasses are simply a collection of ctors which mirror
       specific whio_stream factory functions.
    */
    class InStream : public StreamBase
    {
    protected:
        InStream();
    public:
        virtual ~InStream();
        /**
           Proxies the given whio_stream object. If takeOwnership is
           true then ownership of dev is transfered to this object and
           dev will be destroyed when this object is close()d. If
           takeOwnership is false, ownership is not transfered and
           the stream must outlive this object.

           Throws on error.
         */
        InStream( whio_stream * d, bool takeOwnership );
        /**
           A wrapper around whio_stream_for_dev(). Throws
           if creation of the wrapper fails.
        */
        InStream( whio_dev * d, bool takeOwnership );

        /**
           Initializes the stream to proxy the given device. If
           takeOwnership is true then this object takes ownership of
           d.handle() on success.
        */
        InStream( IODev & d, bool takeOwnership );

        /**
           See whio_stream_api::read().
        */
        whio_size_t read( void * dest, whio_size_t n );
    };

    /**
       The base C++ interface for output whio_stream objects.

       This implementation acts as a wrapper around a raw whio_stream
       object, optionally taking ownership of the stream. Subclasses
       may add type-specific APIs to the interface, but most
       subclasses are simply a collection of ctors which mirror
       specific whio_stream factory functions.
    */
    class OutStream : public StreamBase
    {
    protected:
        OutStream();
    public:
        virtual ~OutStream();
        /**
           Proxies the given whio_stream object. If takeOwnership is
           true then ownership of dev is transfered to this object and
           dev will be destroyed when this object is close()d. If
           takeOwnership is false, ownership is not transfered and
           the stream must outlive this object.

           Throws on error.
         */
        OutStream( whio_stream * d, bool takeOwnership );
        /**
           A wrapper around whio_stream_for_dev(). Throws
           if creation of the wrapper fails.

           If takeOwnership is true then this object takes ownership
           of d on success.
        */
        OutStream( whio_dev * d, bool takeOwnership );

        /**
           Initializes the stream to proxy the given device. If
           takeOwnership is true then this object takes ownership of
           d.handle() on success.
        */
        OutStream( IODev & d, bool takeOwnership );

        /**
           See whio_stream_api::flush().

           Throws on error.
        */
        void flush();
        /**
           See whio_stream_api::write().
        */
        whio_size_t write( void const * src, whio_size_t n );
    };

  
    /**
       Wraps file-backed input streams.
    */
    class FileInStream : public InStream
    {
    public:
        virtual ~FileInStream() {}
        /**
           Wraps the given file in read-only mode.
           Throws on error.
         */
        FileInStream( char const * fname );
        /**
           Wraps the given FILE object. If takeHandle is true
           the this object takes over ownership of f, else
           f must outlive this object.

           Throws on error.
        */
        FileInStream( FILE * f, bool takeHandle );

        /**
           Wraps the given opened file descriptor.

           Throws on error.
        */
        explicit FileInStream( int fileno );
    };

    /**
       Wraps file-backed output streams.
    */
    class FileOutStream : public OutStream
    {
    public:
        virtual ~FileOutStream() {};
        /**
           fname must be a non-NULL/non-empty file name. if truncate
           is true then the file is truncated, else is is appended
           to.

           Throws on error.
        */
        FileOutStream( char const * fname, bool truncate );
        /**
           Wraps the given FILE object. If takeHandle is true
           the this object takes over ownership of f, else
           f must outlive this object.

           Throws on error.
        */
        FileOutStream( FILE * f, bool takeHandle );

        /**
           Wraps the given opened file descriptor.

           Throws on error.
        */
        explicit FileOutStream( int fileno );
    };

    /**
       Wraps various forms of file-backed i/o devices.
    */
    class FileIODev : public IODev
    {
    public:
        virtual ~FileIODev() {}
        /**
           Proxy for whio_dev_for_filename().
        */
        FileIODev( char const * fname, char const * mode );
        /**
           Proxy for whio_dev_posix_open2().
        */
        FileIODev( char const * fname, whio_iomode_mask flags, short perms = 0600 );
        /**
           Proxy for whio_dev_for_FILE().

           Achtung: this device will not be able to report
           its iomode() correctly because it has no way
           to ask the file handle.
         */
        FileIODev( FILE * f, bool takeHandle );
        /**
           Proxy for whio_dev_for_fileno().

           fileno must be an opened file handle identifier.

           Achtung: if mode's open mode does not match fileno's actual
           mode, iomode() will return invalid results (which are based
           on the mode parameter).
        */
        explicit FileIODev( int fileno, char const * mode );
    };

    /**
       Wraps various forms of in-memory i/o devices.
       See the ctors for details.
    */
    class MemoryIODev : public IODev
    {
    private:
        /**
           Throws an exception if !m_io. The given size is
           used in the error message.
        */
        void checkInit(whio_size_t);
    public:
        virtual ~MemoryIODev() {}

        /**
           Proxy for whio_dev_for_membuf().
        */
        explicit MemoryIODev( whio_size_t size, float expFactor = 1.5 );

        /**
           Proxy for whio_dev_for_memmap_rw().
        */
        MemoryIODev( void * mem, whio_size_t size );

        /**
           Proxy for whio_dev_for_memmap_ro().
        */
        MemoryIODev( void const * mem, whio_size_t size );

        /**
           Returns the size of the memory buffer, which is at least as
           large as size(). Dynamic buffers can change size, of
           course.
        */
        whio_size_t bufferSize();

        /**
           Returns a pointer to the start of the memory buffer.  BE
           AWARE that for dynamic emory buffers the memory can by
           invalidated by any write access to the device, as it the
           buffer may get reallocated in order to grow or shrink.
        */
        void const * buffer() const;

    };

    /**
       An IODev which acts as a wrapper around a range of bytes in a
       parent device. See whio_dev_subdev_create().
    */
    class Subdevice : public IODev
    {
    public:
        virtual ~Subdevice() {}
        /**
           Proxy for whio_dev_subdev_create(). parent must be opened
           and must outlive this object.

           Reminder: the range arguments "should arguably" be in the
           form (lowerBound,numberOfBytes), but it is not for
           historical reasons.  Lots of code uses the current
           semantics and i can't just swap them because it would still
           compile (same argument types) but break badly at runtime
           (i.e. it would be difficult to track down and fix all the
           uses).
         */
        Subdevice( IODev & parent, whio_size_t lowerBound, whio_size_t upperBound );

        /**
           Analog to whio_dev_subdev_rebound2(), this re-binds this
           subdevice to the given parent object (which may differ from
           its current parent).

           Throws on error.
        */
        void rebound( IODev & parent, whio_size_t lowerBound, whio_size_t upperBound );

        /**
           Analog whio_dev_subdev_rebound(), this re-sets the bounds
           of the subdevice.

           Throws on error.
        */
        void rebound( whio_size_t lowerBound, whio_size_t upperBound );
    };


    /**
       StdOStreamBuf is a helper to take output send to a std::ostream
       and redirect it to a whio_stream, e.g. so that we can use the
       standard ostream operators for writing to a whio_stream. It
       does this by hijacking the std::stream's buffer, so that all
       output sent to that stream goes to the underlying whio_stream
       instead.

       This object is intended to be used as a proxy, like:

       \code
       whio_stream * outfile = whio_stream_for_file("my.file", "w+");
       std::ostringstream dummy;
       StdOStreamBuf sentry( dummy, out, true );
       ... output to dummy. It goes to outfile instead ...
       // For example:
       s11nlite::save( dummy, myS11nableObject );
       ...
       \endcode

       Limitations: only write is supported. No lookback, no re-get,
       etc.

       When used in conjunction with EPFS pseudofiles, this class can
       drastically (through its buffering) increase throuput compared
       to using many smaller writes.
    */
    class StdOStreamBuf : public std::streambuf
    {
    private:
	struct Impl;
	Impl * impl;
    public:
	typedef std::streambuf::char_type char_type;
	typedef std::streambuf::traits_type traits_type;
        /**
           Default output buffer size, in bytes.
        */
	const static uint32_t DefaultBufSize = 256;

	/**
	   Sets in.rdbuf(this) and sets up to divert all output to
	   whio_out.

           If whio_out does not appear to be opened for read mode, a
           std::exception is thrown.

           std_out must outlive this object.

           If ownsWh is true then this object takes over ownership of
           whio_out and will destroy it when this object is destroyed.
           If ownsWh is false then the caller is responsible for
           ensuring that both streams outlive this object.

           If this constructor throws, ownership of whio_out does not
           change.

           The bufferSize argument specifies the amount of input
           to buffer at a time from the stream. A value of 0
           is legal for this class, in which case a call to
           write() is made for each output byte.
        */
	StdOStreamBuf( std::ostream & std_out,
                       whio_stream * whio_out,
                       bool ownsWh,
                       uint32_t bufferSize = DefaultBufSize );

	/**
	   If the ostream still has this object as its rdbuf() then
	   this function re-sets the rdbuf to its original state. Thus
	   after this, output send to the original std::ostream will
	   go to its originally intended distination.

	   This does not close the associated streams.
	*/
	virtual ~StdOStreamBuf();

    protected:
	/**
	   If !traits_type::not_eof(c) then it writes c to the
	   whio_stream and returns traits_type::not_eof(c), else is
	   has no side-effects and returns traits_type::eof().
	*/
	virtual int overflow(int c);

        /**
           Flushed buffered output to the target stream.
        */
	virtual int sync();

    private:
	//! Copying not allowed.
	StdOStreamBuf( const StdOStreamBuf & );
	//! Copying not allowed.
	StdOStreamBuf & operator=( const StdOStreamBuf & );
    };

    /**
       StdIStreamBuf is a helper to redirect input from a whio_stream
       to a std::istream, e.g. so that we can use the standard
       instream operators for reading from a whio_stream. It does this
       by hijacking the std::stream's buffer, so that all input read
       from that stream comes from the underlying whio_stream.

       This object is intended to be used as a proxy, like:

       \code
       whio_stream * infile = whio_stream_for_filename("my.file","r");
       std::istringstream dummy;
       StdIStreamBuf sentry( dummy, infile, true );
       // Use a 3rd-party API which uses the STL streams:
       s11nlite::node_type * node = s11nlite::load_node(dummy);
       \endcode

       Limitations: only readahead is supported. No lookahead, no
       putback, etc.

       When used in conjunction with EPFS pseudofiles, this class can
       drastically (through its buffering) increase throuput compared
       to using many smaller reads.
    */
    class StdIStreamBuf : public std::streambuf
    {
    private:
	struct Impl;
	Impl * impl;
    public:
	typedef std::streambuf::char_type char_type;
	typedef std::streambuf::traits_type traits_type;
        /**
           Default input buffer size, in bytes.
        */
	const static uint32_t DefaultBufSize = 512;
	/**
	   Sets std_in.rdbuf(this) and sets up to divert
	   all output to whio_in.

           If 

	   If whio_in does not appear to be opened for read mode,
           a std::exception is thrown.

           std_in must outlive this object.

           If ownsWh is true then this object takes over ownership of
           whio_in and will destroy it when this object is destroyed.
           If ownsWh is false then the caller is responsible for
           ensuring that both streams outlive this object.

           If this constructor throws, ownership of whio_in does not
           change.

           The bufferSize argument specifies the amount of input
           to buffer at a time from the stream. A value of 0
           is not legal (causes an exception) because the code
           is not in place to handle that value.
        */
	StdIStreamBuf( std::istream & std_in,
                       whio_stream * whio_in,
                       bool ownsWh,
                       uint32_t bufferSize = DefaultBufSize );
	/**
	   If the istream still has this object as its
	   rdbuf() then this function re-sets the rdbuf
	   to its original state.

	   This does not close the associated streams.
	*/
	virtual ~StdIStreamBuf();

    protected:
	/**
	   Fetches the next character(s) from the whio_stream.
	*/
	virtual int_type underflow();
    private:
	//! Copying not allowed.
	StdIStreamBuf( const StdIStreamBuf & );
	//! Copying not allowed.
	StdIStreamBuf & operator=( const StdIStreamBuf & );
    };

    /**
       A proxy class to allow using std::ostream operations on an
       output-capable whio_stream, and passing a whio_stream to
       routines requiring a std::ostream. All output to this object
       will end up going to the whio_stream.

       Example usage:

       \code
       whio_stream * file = whio_stream_for_filename( "my.file", "r+"));
       StdOStream str(file,true);
       str << "Hi, world!\n";
       \endcode

       FIXME: add an optional output buffer. We currently call write()
       for each byte, which has an espcially high cost on embedded
       whio_dev objects like EPFS pseudofiles.
    */
    class StdOStream : public std::ostream
    {
    public:
	/**
	   Sets up all output to go to proxy.

	   If proxy does not appear to be opened in write mode then a
	   std::exception is thrown.

           If takeOwnership is true then this object takes over
           ownership of proxy and will destroy it when this object is
           destroyed.

           If takeOwnership is false then the caller is responsible
           for ensuring that the proxy stream outlives this object.

           See StdOStreamBuf for the meaning of the bufferSize.
	*/
	StdOStream( whio_stream * proxy, bool takeOwnership,
                    uint32_t bufferSize = StdOStreamBuf::DefaultBufSize );
        /**
           Similar to the whio_stream overload but proxies an
           OutStream object. If takeOwnership is true then
           d.takeHandle() is called to transfer ownership of the
           underlying stream to this object. If this ctor throws then
           ownership is never changed.

           See StdOStreamBuf for the meaning of the bufferSize.
        */
        StdOStream( OutStream & d, bool takeOwnership,
                    uint32_t bufferSize = StdOStreamBuf::DefaultBufSize  );
        /**
           Works like the InStream ctor, but takes an IODev.

           See StdOStreamBuf for the meaning of the bufferSize.
        */
        StdOStream( IODev & d, bool takeOwnership,
                    uint32_t bufferSize = StdOStreamBuf::DefaultBufSize  );
	/**
	   Detaches this object from the constructor-specified proxy.
	*/
	virtual ~StdOStream();
    private:
	//! Copying not allowed.
	StdOStream( StdOStream const & );
	//! Copying not allowed.
	StdOStream & operator=( StdOStream const & );
	StdOStreamBuf m_buf;
    };

    /**
       A proxy class to allow using std::istream operations on an
       input-capable whio_stream, and passing a whio_stream to
       routines requiring a std::istream. All output to this object
       will end up going to the whio_stream.

       Example usage:

       \code
       whio_stream * file = whio_stream_for_filename("my.file","r");
       StdIStream str(file,true);
       some_routine_taking_std_stream( str );
       \endcode
    */
    class StdIStream : public std::istream
    {
    public:
	/**
	   Sets up all output input to go to proxy.

	   If proxy does not appear to be opened in read mode then a
	   std::exception is thrown.

           If takeOwnership is true then this object takes over
           ownership of proxy and will destroy it when this object is
           destroyed.

           If takeOwnership is false then the caller is responsible
           for ensuring that the proxy stream outlives this object.

           See StdIStreamBuf for the meaning of the bufferSize
           argument.
        */
	StdIStream( whio_stream * proxy, bool takeOwnership,
                    uint32_t bufferSize = StdIStreamBuf::DefaultBufSize );
        /**
           Similar to the whio_stream overload but proxies an InStream
           object. If takeOwnership is true then d.takeHandle() is
           called to transfer ownership of the underlying stream to
           this object. If this ctor throws then ownership is never
           changed.

           See StdIStreamBuf for the meaning of the bufferSize
           argument.
        */
        StdIStream( InStream & d, bool takeOwnership,
                    uint32_t bufferSize = StdIStreamBuf::DefaultBufSize );
        /**
           Works like the InStream ctor, but takes an IODev.

           See StdIStreamBuf for the meaning of the bufferSize
           argument.
        */
        StdIStream( IODev & d, bool takeOwnership,
                    uint32_t bufferSize = StdIStreamBuf::DefaultBufSize );
	virtual ~StdIStream();
    private:
	//! Copying not allowed.
	StdIStream( StdIStream const & );
	//! Copying not allowed.
	StdIStream & operator=( StdIStream const & );
	StdIStreamBuf m_buf;
    };

}
#endif /* WANDERINGHORSE_NET_WHIOPP_HPP_INCLUDED */
/* end file include/wh/whio/whiopp.hpp */
/* begin file include/wh/whio/whiopp_util.hpp */
#if defined(__cplusplus)
#if !defined(WANDERINGHORSE_NET_WHIOPP_UTIL_HPP_INCLUDED)
#define WANDERINGHORSE_NET_WHIOPP_UTIL_HPP_INCLUDED
#include <vector> /* only for a buffering workaround/kludge. */
#include <iterator>
#include <algorithm>
#include <cassert>

namespace whio {

    using ::whio_mutex;
    using ::whio_ht;

    /**
       This class wraps the whio_ht class, simplifying
       its usage a bit.
    */
    class HashTable
    {
    private:
        whio_ht m_ht;
        HashTable();
        //! Not implemented.
        HashTable( HashTable const & );
        //! Not implemented.
        HashTable & operator=(HashTable const &);
        //! Throws if m_ht is not opened.
        void assertOpen() const;
    public:
        /**
           Calls close() to free up any resources.
         */
        ~HashTable();

        /**
           A collection of options for use
           with format().
        */
        struct FormatOpt
        {
            /**
               Hash table size.
             */
            whio_size_t hashSize;
            /**
               Optional mutex. It need not support recursive locks,
               but note that some hashtable operations are not atomic
               vis-a-vis the mutex. e.g. remove-then-insert.
             */
            whio_mutex mutex;
            /**
               See whio_ht_funcset_register() and
               whio_ht_funcset_search().

               The default value is "string" (case-sensitive string
               hashing).
            */
            char const * functionSet;

            /**
               Initializes all properties to some reasonably
               sane defaults.
             */
            FormatOpt();
        };

        /**
           A Record holds metadata related to a hashtable entry.
           These objects hold only storage-related identifiers, and
           not the actual raw data (which is still on storage at this
           point).
        */
        class Record
        {
        private:
            friend class HashTable;
            HashTable * m_ht;
            whio_ht_record m_rec;
            void assign( HashTable *, whio_ht_record const & );
        public:
            Record();
            bool isEmpty() const;
#if 0
            /**
               Returns the low-level whio_epfs handle. Ownership is not
               transfered by this call and clients MUST NOT destroy the
               object or transfer ownership of it elsewhere.
            */
            whio_ht_record * handle();
#endif
            /**
               Const-correct overload.
            */
            whio_ht_record const * handle() const;
            /**
               Removes this record from the hashtable. Throws on error.
            */
            void remove();
            whio_size_t keyLength() const;
            whio_size_t valueLength() const;

            /**
               Copies all bytes of this record's key to the given
               output iterator. If nulTerminate is true then an extra
               NUL byte is added to the end of the string (whio_ht
               treats data as opaque and does not automatically
               NUL-terminate them).

               Throws on error.

               FIXME: whio_ht doesn't have any streaming output ops
               like whio_vlbm does, so we have to buffer :(.

               Note that when using non-string keys, this gets
               a bit ugly. In that case we need to pass a pointer
               (or iterator) to the raw bytes of the value. For example,
               here's a case which uses (int32_t const *) keys:

               @code
               HashTable::FormatOpt htopt;
               htopt.functionSet = "int32_t*";
               HashTable * ht = HashTable::format( myDevice, htopt );
               int32_t vals[] = {1,2,3,4,5};
               whio_size_t const sz = sizeof(uint32_t);
               ht->insert(&vals[0],sz,"aAa",3);
               ht->insert(&vals[1],sz,"bBb",3);
               ht->insert(&vals[2],sz,"cCc",3);
               HashTable::Record rec;
               assert( ht->search(&vals[1],sz,rec) );
               int32_t key = 0;
               unsigned char * iter = (unsigned char *)&key;
               rec.copyKey( iter, false );
               assert( 2 == key );
               @endcode

               But note that that example relies on the platform's
               byte ordering, and is not portable across
               architectures. A more portable approach would
               encode/decode the integer values into a
               platform-neutral format (e.g. using the whio_encode.h
               API).
            */
            template <typename OutputIter>
            void copyKey( OutputIter it, bool nulTerminate = false ) const
            {
                typedef std::vector<char> Vec;
                Vec vec(m_rec.keyLen + (nulTerminate ? 1 : 0), 0);
                whio_size_t kLen = m_rec.keyLen;
                int const rc = whio_ht_key_get_n( &m_ht->m_ht, &m_rec,
                                                  &vec[0], &kLen);
                if( rc ) throw RcException("whio_ht_key_get_n",rc);
                assert( kLen == m_rec.keyLen );
                std::copy( vec.begin(), vec.end(), it );
            }

            /**
               Copies all bytes of this record's value to the given
               output iterator. If nulTerminate is true then an extra
               NUL byte is added to the end of the string (whio_ht
               treats data as opaque and does not automatically
               NUL-terminate them).

               Throws on error.

               FIXME: whio_ht doesn't have any streaming output ops
               like whio_vlbm does, so we have to buffer :(.
            */
            template <typename OutputIter>
            void copyValue( OutputIter it, bool nulTerminate = false ) const
            {
                typedef std::vector<char> Vec;
                Vec vec(m_rec.valueLen + (nulTerminate ? 1 : 0), 0);
                whio_size_t len = m_rec.valueLen;
                int const rc = whio_ht_value_get_n( &m_ht->m_ht, &m_rec,
                                                    &vec[0], &len);
                if( rc ) throw RcException("whio_ht_key_get_n",rc);
                assert( len == m_rec.valueLen );
                std::copy( vec.begin(), vec.end(), it );
            }

#if 0
            void value( void * dest, whio_size_t * n );
            void value( void * dest );
            void key( void * dest, whio_size_t * n );
            void key( void * dest );
#endif
        };

        /**
           Works like the format() overload taking the same parameters.
        */
        HashTable( whio_dev * dev, HashTable::FormatOpt const & opt );
        /**
           Works like the format() overload taking the same parameters.
        */
        HashTable( IODev & dev, HashTable::FormatOpt const & opt );
        /**
           Works like the open() overload taking the same parameters.
        */
        HashTable( IODev & dev );
        /**
           Works like the open() overload taking the same parameters.
        */
        HashTable( whio_dev * dev );

        /**
           "Formats" dev, which must be a writable device,
           for use as a hashtable. This irrevocably destroys
           all data on dev!

           On success a new HashTable is returned and ownership of dev
           is transfered to that object. There is currently no way to
           regain ownership of dev downstream.

           The FormatOpt objects defines the hashtable's parameters,
           and the options mimic those used by whio_ht_format().
        */
        static HashTable * format( whio_dev * dev,
                                   FormatOpt const & opt = FormatOpt() );

        /**
           Overloaded to take ownership of dev.handle() on success. If
           format() throws, ownership is not changed. On success,
           dev.handle() will be NULL and ownership of the underlying
           handle is passed to the returned HashTable object.

           Sample usage:

           @code
           FileIODev infile( "foo.ht", WHIO_MODE_RWC );
           HashTable * ht = HashTable::format( infile );
           // infile is now an empty shell, as we transfered
           // ownership of infile.handle() to ht.
           @endcode
        */
        static HashTable * format( IODev & dev,
                                   FormatOpt const & opt = FormatOpt() );

        /**
           Analog to whio_ht_open(). On success ownership of dev is
           transfered to the returned HashTable object. The returned
           object is owned by the caller and must eventually be
           deleted. On error ownership of dev is not changed.

           See format() for more details.

           If dev is read-only then write operations on the
           EFS will fail.
        */
        static HashTable * open( whio_dev * dev );

        /**
           Overloaded to take ownership of dev.handle() on success. If
           open() throws, ownership is not changed. On success,
           dev.handle() will be NULL and ownership of the underlying
           handle is passed to the returned HashTable object.
        */
        static HashTable * open( IODev & dev );
        /**
           Frees the underlying hashtable resources and
           closes the parent i/o device. After this,
           most other functions in this class will trigger
           an exception when called.
        */
        void close();

        /**
           Returns true if this hashtable has been close()d.
         */
        bool isClosed() const;

        /**
           Returns the on-storage size of the EFS container.
        */
        whio_size_t size();

        /**
           Analog to whio_ht_insert().
        */
        void insert( void const * key, whio_size_t keyLen,
                     void const * value, whio_size_t valueLen );
        /**
           Analog to whio_ht_remove() but with slightly different
           return semanitcs: if a record is found and removed, true is
           returned. If no record is found, false is returned.  For
           any error other than no-record-found, an exception is
           thrown.
        */
        bool remove( void const * key, whio_size_t keyLen );

        /**
           Similar to whio_ht_search() but with slightly different
           semantics...
           
           Searches for the given key. If no record is found, false is
           returned and tgt is not modified.  If a match is found, tgt
           is updated with the record's info (just a small list of
           on-storage locations, not the actual data itself).

           On any error other than "no match found" an exception
           is thrown.
        */
        bool search( void const * key, whio_size_t keyLen, Record & tgt );

        /**
           Returns true if the hashtable contains the given key.
        */
        bool contains(void const * key, whio_size_t keyLen);

        /**
           See whio_ht_opt_set_wipe_on_remove().
        */
        void wipeOnRemove( bool );

        /**
           Returns the low-level whio_ht handle. It is owned by this
           object and clients _must not_ destroy or close this handle.
           Its bytes are valid at least until this object is close()d
           (and possibly until it's destructed, but the API does not
           guaranty that).
        */
        whio_ht * handle();

        /**
           Const-correct overload.
         */
        whio_ht const * handle() const;
    private:
        friend class Record;
        //! Internal open() impl.
        static void open( HashTable &, whio_dev * dev );
        //! Internal open() impl.
        static void open( HashTable &, IODev & dev );
        //! Internal format() impl.
        static void format( HashTable &, whio_dev * dev, FormatOpt const & opt );
        //! Internal format() impl.
        static void format( HashTable &, IODev & dev, FormatOpt const & opt );
    };

    /**
       Experimental - do not use.
    */
    template <typename T>
    struct HTKeyCodec
    {
        typedef T Type;
        static const uint16_t SizeOfEncoded = sizeof(Type);
        bool operator()( Type const & src, void * dest );
        bool operator()( void const * src, Type & dest );
    };

    /**
       Experimental - do not use.
     */
    template <>
    struct HTKeyCodec<int32_t>
    {
        typedef int32_t Type;
        static const uint16_t SizeOfEncoded = whio_sizeof_encoded_int32;
        static const uint16_t SizeOfDecoded = sizeof(Type);

        bool operator()( Type src, void * dest ) const
        {
            return SizeOfEncoded == whio_encode_int32( (unsigned char *)dest, src );
        }

        bool operator()( void const * src, Type & dest ) const
        {
            return 0 == whio_decode_int32( (unsigned char const *)src, &dest );
        }
    };
#define HT_CODEC_IMPL(T,enc_func,dec_func,enc_sizeof)   \
    template <> struct HTKeyCodec< T > { \
        typedef T Type; \
        static const uint16_t SizeOfEncoded = enc_sizeof; \
        bool operator()( Type src, void * dest ) const \
        { return SizeOfEncoded == enc_func( (unsigned char *)dest, src ); } \
        bool operator()( void const * src, Type & dest ) const \
        {return 0 == dec_func( (unsigned char const *)src, &dest );}\
    }

    HT_CODEC_IMPL(int8_t,whio_encode_int8,whio_decode_int8,whio_sizeof_encoded_int8);
    HT_CODEC_IMPL(int16_t,whio_encode_int16,whio_decode_int16,whio_sizeof_encoded_int16);
    //HT_CODEC_IMPL(int32_t,whio_encode_int32,whio_decode_int32,whio_sizeof_encoded_int32);
    HT_CODEC_IMPL(int64_t,whio_encode_int64,whio_decode_int64,whio_sizeof_encoded_int64);
    
    HT_CODEC_IMPL(uint8_t,whio_encode_uint8,whio_decode_uint8,whio_sizeof_encoded_uint8);
    HT_CODEC_IMPL(uint16_t,whio_encode_uint16,whio_decode_uint16,whio_sizeof_encoded_uint16);
    HT_CODEC_IMPL(uint32_t,whio_encode_uint32,whio_decode_uint32,whio_sizeof_encoded_uint32);
    HT_CODEC_IMPL(uint64_t,whio_encode_uint64,whio_decode_uint64,whio_sizeof_encoded_uint64);
#undef HT_CODEC_IMPL

    /**
       Experimental - do not use.
     */
    template <typename FixedSizeKeyType>
    struct HTKeyTypeName
    {
        const static char * Name;
    };

#define HT_TYPE_NAME_DECL(T) template <> \
    struct HTKeyTypeName< T > { const static char * Name; }
    HT_TYPE_NAME_DECL(int8_t);
    HT_TYPE_NAME_DECL(uint8_t);
    HT_TYPE_NAME_DECL(int16_t);
    HT_TYPE_NAME_DECL(uint16_t);
    HT_TYPE_NAME_DECL(int32_t);
    HT_TYPE_NAME_DECL(uint32_t);
    HT_TYPE_NAME_DECL(int64_t);
    HT_TYPE_NAME_DECL(uint64_t);
#undef HT_TYPE_NAME_DECL

    /**
       Experimental - do not use.
     */
    template <typename FixedSizeKeyType>
    class HTKeyHelper
    {
    public:
        typedef FixedSizeKeyType KeyType;
    private:
        typedef HTKeyCodec<FixedSizeKeyType> Codec;
        Codec m_c;
        HashTable * m_ht;
        unsigned char m_buf[Codec::SizeOfEncoded];
        inline void enc( KeyType k )
        {
            if( ! m_c(k, m_buf) )
            {
                throw RcException("HTKeyHelper::enc",
                                  whio_rc.ConsistencyError,
                                  "Encoding of key failed.");
            }
        }
    public:
        explicit HTKeyHelper( HashTable & ht )
            : m_c(),
              m_ht(&ht)
        {}

        void reassign( HashTable & ht )
        {
            m_ht = &ht;
        }

        inline void insert( KeyType key, void const * value, whio_size_t valueLen )
        {
            enc(key);
            m_ht->insert( m_buf, Codec::SizeOfEncoded, value, valueLen );
        }
        inline bool remove( KeyType key )
        {
            enc(key);
            return m_ht->remove( m_buf, Codec::SizeOfEncoded );
        }

        inline bool search( KeyType key, HashTable::Record & tgt )
        {
            enc(key);
            return m_ht->search( m_buf, Codec::SizeOfEncoded, tgt );
        }

        inline bool contains( KeyType key )
        {
            enc(key);
            return m_ht->contains( m_buf, Codec::SizeOfEncoded );
        }

        KeyType key( HashTable::Record const & rec )
        {
            if( Codec::SizeOfEncoded != rec.keyLength() )
            {
                throw RcException("HTKeyHelper::key",
                                  whio_rc.RangeError,
                                  "Key type and record key size do not match.");
            }
            int const rc =
                whio_ht_key_get_n( m_ht->handle(), rec.handle(),
                                   m_buf, NULL );
            if( rc )
            {
                throw RcException("HTKeyHelper::key",
                                  rc,
                                  "Fetching of key data failed.");
            }
            KeyType k = 0;
            if( ! m_c(m_buf,k) )
            {
                throw RcException("HTKeyHelper::key",
                                  whio_rc.ConsistencyError,
                                  "Decoding of key data failed.");
            }
            return k;
        }
    };
}

#endif /* include guard */
#endif /* C++ guard */
/* end file include/wh/whio/whiopp_util.hpp */
/* begin file include/wh/whio/whiopp_epfs.hpp */
#if defined(__cplusplus) && !defined(WANDERINGHORSE_NET_WHIOPP_EPFS_HPP_INCLUDED)
#define WANDERINGHORSE_NET_WHIOPP_EPFS_HPP_INCLUDED

#include <string>

namespace whio {

    using ::whio_epfs;
    using ::whio_epfs_id_t;
    using ::whio_epfs_fsopt;

    /**
       This class wraps the majority of the whio_epfs API. Each
       instance of this class represents one whio_epfs instance.

       New instances are generally created via the mkfs() and openfs()
       family of static member functions, but there are constructors
       which mimic those behaviours. i personally recommend using
       mkfs() and openfs() because its clearer to those reading the
       code what the destructive operation (in the case of mkfs()) is
       happening. Nonetheless, the ctors allow stack allocation of
       EPFS instances, whereas mkfs() and openfs() do not.
    */
    class EPFS
    {
    private:
        whio_epfs m_fs;
        static whio_epfs_fsopt const * defaultFsOpt();
        //! Throws if m_fs is not opened.
        void assertOpen() const;
        EPFS();
        //! Not implemented.
        EPFS(EPFS const &);
        //! Not implemented.
        EPFS & operator=(EPFS const &);
    public:
        /**
           Works like the mkfs() overload taking the same
           arguments. Throws on error.
        */
        EPFS( whio_dev * dev, bool takeStore, whio_epfs_fsopt const * opt );
        /**
           Works like the mkfs() overload taking the same
           arguments. Throws on error.
        */
        EPFS( char const * filename, bool allowOverwrite, whio_epfs_fsopt const * fsopt );
        /**
           Works like the openfs() overload taking the same
           parameters.
        */
        EPFS( whio_dev * store, bool takeStore );
        /**
           Works like the openfs() overload taking the same parameters.
        */
        EPFS( char const * filename, bool writeMode );
        /**
           Closes the EFS and releases all resources.

           See close().
        */
        ~EPFS();
        /**
           PseudoFiles are files which live inside
           an EPFS container. This class provides
           access to their contents via the IODev
           interface.

           These objects are only created via
           EPFS::open().

           ACHTUNG: _ALL_ PseudoFiles opened from a given EPFS
           instance _MUST_ have been close()d or deleted before that
           instance is close()d or deleted or Undefined Behaviour
           ensues.
        */
        class PseudoFile : public IODev
        {
        private:
            EPFS & m_fs;
            /**
               Only called by EPFS::openXXX().
             */
            PseudoFile(EPFS & fs, whio_dev *d);
            friend class EPFS;
        public:
            virtual ~PseudoFile();

            /**
               Returns this object's inode ID.
            */
            whio_epfs_id_t inodeId() const;

            //whio_epfs_inode * inode();

            /**
               Returns this object's raw inode.
            */
            whio_epfs_inode const * inode() const;

            /**
               Updates the modification time to the given timestamp
               (GMT) or the current time if time==-1.
             */
            void touch( uint32_t time = (uint32_t)-1 );

            /**
               Fetches the last modification time
               (it _should_ be in GMT).
             */
            uint32_t mtime() const;

            /** Sets the client-defined flags. */
            void clientFlags( uint32_t val );

            /** Fetches the client-defined flags. */
            uint32_t clientFlags() const;

            /** Sets the inode's name. Fails if it is opened
                read-only or if hasNamer() is false.
 
            */
            void name( char const * name );
            /**
               Fetches the inode's name, if any. Throws if there is no
               namer installed in the EFS.  Note that empty names are
               legal in EFS.
            */
            std::string name();

            /**
               Returns true if this inode is marked as "internal"
               (e.g. potentially an inode allocated by a namer).
            */
            bool isInternal() const;
        };

        /**
           Equivalent to whio_epfs_mkfs2(), but reports errors via
           exceptions and returns a new EPFS instance on success.

           This irrevocably destroys all data on dev!

           If takeStore is true then on success ownership of dev is
           passed to the returned object (and there is no way to
           relinquish it), otherwise dev must outlive the returned
           object.
        */
        static EPFS * mkfs( whio_dev * dev, bool takeStore, whio_epfs_fsopt const * opt );

        /**
           Equivalent to whio_epfs_mkfs_file(), but reports errors via
           exceptions and returns a new EPFS instance on success.

           This irrevocably destroys all data on dev!
        */
        static EPFS * mkfs( char const * filename, bool allowOverwrite,
                            whio_epfs_fsopt const * fsopt );

        /**
           Roughly equivalent to whio_epfs_namer_format(). If used at all,
           it should be used immediately after mkfs().

           See whio_epfs_namer_reg, whio_epfs_namer_reg_search(), and
           whio_epfs_namer_add() for more details.
        */
        void installNamer( char const * impl = "ht" );

        /**
           Equivalent to whio_epfs_openfs2(). Returns the new instance
           (owned by the caller) on success. Throws on error.

           If takeStore is true then on success ownership of dev is
           passed to the returned object (and there is no way to
           relinquish it), otherwise dev must outlive the returned
           object.
        */
        static EPFS * openfs( whio_dev * store, bool takeStore );

        /**
           Equivalent to whio_epfs_openfs_file(). Returns the new
           instance (owned by the caller) on success. Throws on error.
        */
        static EPFS * openfs( char const * filename, bool writeMode );

        /**
           Returns true if this EFS was opened in read/write mode,
           else false.
        */
        bool isRW() const;

        /**
           Flushes the EFS. Normally not necessary, as it is flushed
           automatically as PseudoFiles are updated.
         */
        void flush();

        /**
           Returns the current block count in the EFS container.
           This does not distinguish between used/unused blocks.
        */
        whio_epfs_id_t currentBlockCount() const;

        /**
           Returns the underlying EPFS options for this instance.
           Never returns NULL and the bytes are valid at least until
           this object is close()d (and possibly even until it's
           deleted, but we won't guaranty that).
        */
        whio_epfs_fsopt const * fsopt() const;

        /**
           Closes the EFS container and frees all resources.

           close() does not free _this_ object, only the interal data
           it refers to.

           Calling this multiple times is a no-op after the first
           call.

           ACHTUNG #1: _ALL_ PseudoFiles opened via this EFS _MUST_
           have been close()d or deleted before this is triggered or
           undefined behaviour ensues.

           ACHTUNG #2: any further calls on this object, other than
           the destructor, will almost certainly cause an exception to
           be thrown.
        */
        void close() throw();

        /**
           Equivalent to whio_epfs_dev_open().

           Throws on error. On success the caller owns the returned
           object and _must_ delete it _before_ this EPFS instance is
           closed.

           Reminder: i can't overload open() because the value 0 is
           both a legal inodeID value and a syntactically legal
           c-string literal (but not semantically legal in this case),
           so it is ambiguous :/.
        */
        PseudoFile * openById( whio_epfs_id_t inodeID, whio_iomode_mask mode );

        /**
           Equivalent to whio_epfs_dev_open_by_name().

           Note that naming support is optional in an EFS, and this
           will throw if no namer has been installed.
           
           Throws on error. On success the caller owns the returned
           object and _must_ delete it _before_ this EPFS instance is
           closed.
        */
        PseudoFile * openByName( char const * name, whio_iomode_mask mode );

        /**
           Removes the pseudofile with the given inode ID.
           See whio_epfs_unlink() for the limitations and
           error conditions.

           Throws on error.
        */
        void unlink( whio_epfs_id_t inodeID );

        /**
           Removes the pseudofile with the given name.  See
           whio_epfs_unlink_by_name() for the limitations and error
           conditions.

           Throws on error.
        */
        void unlink( char const * name );

        /**
           Returns the low-level whio_epfs handle. Ownership is not
           transfered by this call and clients MUST NOT destroy the
           object or transfer ownership of it elsewhere.
        */
        whio_epfs * handle();

        /**
           Const-correct overload.
        */
        whio_epfs const * handle() const;

        /**
           Sets the EPFS label. See whio_epfs_label_set() for
           the limitations and error conditions.

           Throws on error.
        */
        void label( char const * lbl );

        /**
           Fetches the EPFS label. See whio_epfs_label_get()
           for details. Throws on error. An empty label
           is legal.
        */
        std::string label();

        /**
           Returns true if this EPFS has a "namer" installed.
           There is currently no API to remove or replace
           an installed namer.
        */
        bool hasNamer() const;

        /**
           Sets the name of the given inode ID.  See
           whio_epfs_name_set() for details.

           name must be NULL (to unset the name) or a NUL-terminated
           string. The underlying whio_epfs_namer implementation might
           impose an upper limit on the length of the name - if it
           does an exception will be thrown if name is too long.

           Note that this will always throw if !hasNamer().
         */
        void name( whio_epfs_id_t inodeID, char const * name );

        /**
           Fetches the name of the given inode.  See
           whio_epfs_name_get() for details and error conditions.

           Throws on error. An empty name is not technically illegal
           since naming inodes optional.

           Note that this will always throw if !hasNamer().

           If an EFS-side string is larger than some hard internal
           limit (currently 2k) then this function will fail, possibly
           catastrophically. FIXME: 
        */
        std::string name( whio_epfs_id_t inodeID );

        /**
           Searches for the inode with the given name.

           Returns the inode ID on success. This function treats
           no-entry-found as a non-error and returns the value 0 for
           that case (note that 0 is not a valid inode number).

           Throws on any error other than "not found".
        */
        whio_epfs_id_t inodeId( char const * name );

        /**
           Returns true if this object's underlying EPFS has been
           closed (i.e. if close() has been called). This is one of
           the very few functions which does not throw after close()
           has been called.
        */
        bool isClosed() const;

        /**
           Returns the on-storage size of the EFS container.
        */
        whio_size_t size();

    private:
        //! Internal mkfs() impl.
        static void mkfs( EPFS & fs, whio_dev * d, bool takeStore, whio_epfs_fsopt const * opt );
        //! Internal mkfs() impl.
        static void mkfs( EPFS & fs, char const * filename, bool allowOverwrite, whio_epfs_fsopt const * opt );
        //! Internal openfs() impl.
        static void openfs( EPFS & fs, whio_dev * store, bool takeStore );
        //! Internal openfs() impl.
        static void openfs( EPFS & fs, char const * filename, bool writeMode );

    };
    
} // namespaces

#endif /* include guard */
/* end file include/wh/whio/whiopp_epfs.hpp */
