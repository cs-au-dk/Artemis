#if !defined(V8_CONVERT_SOCKET_HPP_INCLUDED)
#define V8_CONVERT_SOCKET_HPP_INCLUDED
/** LICENSE

    This software's source code, including accompanying documentation and
    demonstration applications, are licensed under the following
    conditions...

    The author (Stephan G. Beal [http://wanderinghorse.net/home/stephan/])
    explicitly disclaims copyright in all jurisdictions which recognize
    such a disclaimer. In such jurisdictions, this software is released
    into the Public Domain.

    In jurisdictions which do not recognize Public Domain property
    (e.g. Germany as of 2011), this software is Copyright (c) 2011
    by Stephan G. Beal, and is released under the terms of the MIT License
    (see below).

    In jurisdictions which recognize Public Domain property, the user of
    this software may choose to accept it either as 1) Public Domain, 2)
    under the conditions of the MIT License (see below), or 3) under the
    terms of dual Public Domain/MIT License conditions described here, as
    they choose.

    The MIT License is about as close to Public Domain as a license can
    get, and is described in clear, concise terms at:

    http://en.wikipedia.org/wiki/MIT_License

    The full text of the MIT License follows:

    --
    Copyright (c) 2011 Stephan G. Beal (http://wanderinghorse.net/home/stephan/)

    Permission is hereby granted, free of charge, to any person
    obtaining a copy of this software and associated documentation
    files (the "Software"), to deal in the Software without
    restriction, including without limitation the rights to use,
    copy, modify, merge, publish, distribute, sublicense, and/or sell
    copies of the Software, and to permit persons to whom the
    Software is furnished to do so, subject to the following
    conditions:

    The above copyright notice and this permission notice shall be
    included in all copies or substantial portions of the Software.

    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
    EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
    OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
    NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
    HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
    WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
    FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
    OTHER DEALINGS IN THE SOFTWARE.

    --END OF MIT LICENSE--

    For purposes of the above license, the term "Software" includes
    documentation and demonstration source code which accompanies
    this software. ("Accompanies" = is contained in the Software's
    primary public source code repository.)

*/


#include <stdio.h> // FILE and friends
#include <errno.h>
#include <sstream>
#include <vector>

#ifdef windows
// The windows code is 100% untested!
#  include <winsock2.h>
#  include <ws2tcpip.h>
#else
#  include <unistd.h>
#  include <sys/socket.h>
#  include <sys/un.h>
#  include <sys/param.h>
#  include <arpa/inet.h>
#  include <netinet/in.h>
#  include <netdb.h>
#endif

#include <v8.h>
#include "cvv8/ClassCreator.hpp"
namespace cvv8 {

class JSSocket;
template <>
struct NativeToJS< JSSocket >;
template <>
struct ClassCreator_Factory<JSSocket>;


/**
   A thin wrapper around socket() and friends, providing
   a C++/JS binding for the v8-juice framework.
*/
class JSSocket
{
public:
    static bool enableDebug;
private:
    int fd;
    int family;
    int proto;
    int type;
    bool hitTimeout;
    /* We only set pipeName for AF_UNIX server sockets so we can remove()
        the pipe file when closing the server.
    */
    std::string pipeName;
    friend class NativeToJS< JSSocket >;
    friend class ClassCreator_Factory<JSSocket>;
    /** JS-side 'this' object. Set by ClassCreator_WeakWrap<JSSocket>::Wrap()
        and used by NativeToJS<JSSocket>.
    */
    v8::Handle<v8::Object> jsSelf;

private:
    void init(int family, int type, int proto, int socketFD );
public:
    /**
       Like socket(family,type,proto). If socketFD is >=0 then it is
       assumed to be an opened socket with the same family, type, and
       protocol. If socketFD is (>=0) and the constructor succeeds,
       this object takes ownership of the socket and will close it
       when it destructs. If socketFD is (>=0) and the ctor fails
       (throws), the caller owns the socket.
    */
    JSSocket(int family = AF_INET,
             int type = SOCK_STREAM,
             int proto = 0,
             int socketFD = -1 );

    /** Closes the socket. */
    virtual ~JSSocket();

    /**
       Closes the socket (if it is opened).
    */
    void close();

    /** toString() for JS. */
    std::string toString() const;

    /**
       Installs this class' bindings into dest.

       JS Classes:

       - Socket

       Socket ctor properties:
   
       - int AF_INET
       - int AF_INET6
       - int AF_UNIX
       - int AF_UNSPEC
       - int SOCK_DGRAM
       - int SOCK_STREAM
       - int SOCK_SEQPACKET
       - int SOCK_RAW
   
       Socket class functions:

       - new Socket( [int family=AF_INET [, int type=SOCK_STREAM [, int protocol=0]]] )
       - void close()
       - string toString()
       - int bind( string hostNameOrAddress, int port )
       - int connect( string hostNameOrAddress, int port )
       - string nameToAddress(string host)
       - string addressToName(string address)
       - string read(unsigned int length)
       - int write(string|ByteArray data [,int length=data.length])
       - int setTimeout( unsigned int seconds[, unsigned int microseconds=0] )
       - int setTimeoutMs( unsigned int ms )

       Most of the functions throw on error.

       Socket instance properties:

       - Array[address,port] peerInfo, only valid after a connection is
       established.
   
   
       Socket constructor properties:

       - int getProtoByName( string protocolName )
       - string nameToAddress( string hostname )
       - string addressToName( string address )
   
    */
    static void SetupBindings( v8::Handle<v8::Object> const & dest );

    /**
       JS Usage:

       int bind( string hostNameOrAddress, int port )
    
       Throws a JS exception on error, so the return value
       is largely irrelevant. But 0==success, if you must
       know.       
    */
    int bind( char const * where, int port );

    /**
       JS usage:

       int listen( [int backlog] )

       Throws a JS exception on error. Returns 0 on success.
    */
    int listen( int backlog );

    /** this->listen( someUnspecifiedValue ). */
    int listen();

    /**
       accept(2)'s a connection and creates a new socket
       for it. The returned object is owned by v8.

       Returns NULL if:

       - accept()ing would block a non-blocking socket.

       - Possibly if a timeout occurs.

       On error: in addition to returning NULL, a JS-side exception is
       thrown if accept(2) returns an error or if construction of the
       new socket object fails for some reason.
    */
    JSSocket * accept();

    static int getProtoByName( char const * name );

    /** Converts name to canonical address. */
    static v8::Handle<v8::Value> nameToAddress( char const * name, int family );

    static v8::Handle<v8::Value> nameToAddress( char const * name );
    /** Converts canonical address addy to hostname. if family==0 then
        AF_INET is assumed. */
    static v8::Handle<v8::Value> addressToName( char const * addy, int family );
    static v8::Handle<v8::Value> addressToName( char const * addy );

    /**
       JS usage:

       int connect( string nameOrAddress, int port )

       Throws a JS exception on error.
    */
    int connect( char const * where, int port );
    
    /**
        Equivalent to this->connect(addr,0).
    */
    int connect( char const * addr );

    /**
        Returns this environment's host name, as reported by
        gethostname(). On error it triggers a JS exception before
        returning.
    */
    static std::string hostname();
    
    /**
       Reads n bytes from the socket and returns them
       as described below.

       Special return values:

       - (val===null) means reading was interrupted by a timeout and 
       no bytes were read before the timeout expired (is that really 
       true???), or another low-level signal interrupted the read 
       (e.g. SIGINT).

       - (val===undefined) EOF.

       If binary is true then the returned value is a ByteArray 
       object. If binary is false then the data is returned as a 
       string (which has Undefined Behaviour if the string is not 
       encoded in a way which v8 requires (UTF-8)).
       
       When the length of the returned data is less than n, it
       could mean any of:

       - Timeout was reached after reading some bytes.

       - EOF
       
       - In non-binary mode, the length of the string can be shorter
       than the number of bytes (UTF-8, remember?).

       There is unfortunately currently no way to 100% reliably 
       distinguish between the first two. i don't know of a way to 
       distinguish when a partial read is partial because of a 
       timeout (there probably is one, though).
       
       BIG FAT HAIRY WARNING:
       
       If binary is false and the read-in block ends in the middle
       of a multi-byte UTF8 character then results are technically
       undefined because that (incomplete/invalid) string will be given
       to the v8 String constructor.
       
       The same applies when using ByteArray.stringValue to append
       the results of reads to a string.
    */
    v8::Handle<v8::Value> read( unsigned int n, bool binary );

    /** this->read( n, false ). */
    v8::Handle<v8::Value> read( unsigned int n );

    /**
       Writes n bytes from src to this socket. Returns the number
       of bytes written or:

       - 0 if a timeout was hit before sending any bytes.

       - It return 0 and throws a JS exception on a write error other
       than timeout-before-send.

       Return of (<n) _may_ be due to a timeout during write.
    */
    unsigned int write2( char const * src, unsigned int n );

    /** this->write2( src, strlen(src) ), or 0 if !src or !*src. */
    unsigned int write1( char const * src );

    /**
       JS usage:

       int write( ByteArray|string src,  [, int len=src.length] )

       Returns number of bytes written. Return of 0 "should" signify
       that a timeout was encountered before any bytes were written. A
       short write _might_ signify that a timeout was encountered
       after some bytes had been written.

       Throws a JS-side exception on write errors other than timeouts.

       argv.This() must be-a JSSocket or it throws a JS-side
       exception.
    */
    static v8::Handle<v8::Value> writeN( v8::Arguments const & argv );

    /**
       JS Usage:

       int sendTo( string hostNameOrAddress, int port, ByteArray|string src [, int len=src.length] );

    */
    static v8::Handle<v8::Value> sendTo( v8::Arguments const & argv );

    
    /**
       JS Usage:

       Array peerInfo()

       Returns [address,port] for AF_INET and AF_INET6 sockets.
       For AF_UNIX sockets, [socketFilePath]. Returns undefined
       for other types.

       This value is only valid after a connection is established,
       and it throws if getpeername(2) fails.
    */    
    v8::Handle<v8::Value> peerInfo();

    /**
       Don't use. See getOpt() for why.
    */
    int setOpt( int key, int val );

    /**
       Don't use this until we can confirm which options we can
       support here.
    */
    v8::Handle<v8::Value> getOpt( int key );
    /**
       Don't use this: the returned string is not going to be encoded
       properly.
    */
    v8::Handle<v8::Value> getOpt( int key, unsigned int len );

    /**
       Sets the send/receive timeouts to the given number of
       seconds/microseconds. Returns 0 on success or an errno value on
       error.
    */
    int setTimeout( unsigned int seconds, unsigned int usec );

    /**
       Equivalent to setTimeout(seconds,0).
    */
    int setTimeoutSec( unsigned int seconds );

    /**
       Sets the socket timeout value in milliseconds.
    */
    int setTimeoutMs( unsigned int ms );

}/*JSSocket*/;

template <>
struct TypeName<JSSocket>
{
    const static char * Value;
};
template <>
struct ClassCreator_Factory<JSSocket>
{
    typedef JSSocket * ReturnType;
    static ReturnType Create( v8::Handle<v8::Object> & jsSelf, v8::Arguments const & argv );
    static void Delete( JSSocket * obj );
};

template <>
struct JSToNative< JSSocket > : JSToNative_ClassCreator< JSSocket >
{};

template <>
struct NativeToJS< JSSocket >
{
    typedef JSSocket * ArgType;
    v8::Handle<v8::Value> operator()( ArgType x ) const;
};
template <>
struct ClassCreator_SetupBindings<JSSocket> : ClassCreator_SetupBindings_ClientFunc<JSSocket,&JSSocket::SetupBindings>
{};

}

#endif
