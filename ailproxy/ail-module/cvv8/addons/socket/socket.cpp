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

#include <cvv8/convert.hpp>
#include <cvv8/ClassCreator.hpp>
#include <cvv8/properties.hpp>
#include <cstdio> // remove()
#include "socket.hpp"
#include "bytearray.hpp"

#if defined(windows)
#  define USE_SIGNALS 0
#  define CloseSocket ::closesocket
#else
#  define USE_SIGNALS 1
#  define CloseSocket ::close
#endif

#include <iostream> // only for debuggering
#define CERR std::cerr << __FILE__ << ":" << std::dec << __LINE__ << ":" <<__FUNCTION__ << "(): "
#define DBGOUT if(cv::JSSocket::enableDebug) CERR
#define JSTR(X) v8::String::New(X)
namespace cv = cvv8;
bool cv::JSSocket::enableDebug = false;


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

char const * cv::TypeName<cv::JSSocket>::Value = "Socket";

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



#ifndef MAXHOSTNAMELEN
#  define MAXHOSTNAMELEN 64
#endif


namespace {

typedef union sock_addr {
    struct sockaddr_in in;
#ifndef windows
    struct sockaddr_un un;
#endif
    struct sockaddr_in6 in6;
} sock_addr_t;

static struct 
{
    /** Name of JSSocket-internal field for holding connection peer information. */
    char const * fieldPeer;
} socket_strings =
    {
    "dgramPeer"
    };
} /* anon namespace */



/**
 * Universal address creator.
 * @param {char *} address Stringified address
 * @param {int} port Port number
 * @param {int} family Address family
 * @param {sock_addr_t *} result Target data structure
 * @param {socklen_t *} len Result length
 */
static int create_addr(char const * address, int port, int family, sock_addr_t * result, socklen_t * len)
{
    unsigned int length = strlen(address);
    switch (family) {
#ifndef windows
      case AF_UNIX: {
          struct sockaddr_un *addr = (struct sockaddr_un*) result;
          memset(addr, 0, sizeof(sockaddr_un));
          
          if (length >= sizeof(addr->sun_path)) {
              cv::Toss("Unix socket path too long");
              return 1;
          }
          addr->sun_family = AF_UNIX;
          memcpy(addr->sun_path, address, length);
          addr->sun_path[length] = '\0';
          *len = length + (sizeof(*addr) - sizeof(addr->sun_path));
      } break;
#endif
      case AF_INET: {
          struct sockaddr_in *addr = (struct sockaddr_in*) result;
          memset(result, 0, sizeof(*addr)); 
          addr->sin_family = AF_INET;

#ifdef windows
          int size = sizeof(struct sockaddr_in);
          int pton_ret = WSAStringToAddress(address, AF_INET, NULL, (sockaddr *) result, &size);
          if (pton_ret != 0) { return 1; }
#else 
          int pton_ret = inet_pton(AF_INET, address, & addr->sin_addr.s_addr);
          if (pton_ret == 0) { return 1; }
#endif

          addr->sin_port = htons((short)port);
          *len = sizeof(*addr);
      } break;
      case AF_INET6: {
          struct sockaddr_in6 *addr = (struct sockaddr_in6*) result;
          memset(addr, 0, sizeof(*addr));
          addr->sin6_family = AF_INET6;

#ifdef windows
          int size = sizeof(struct sockaddr_in6);
          int pton_ret = WSAStringToAddress(address, AF_INET6, NULL, (sockaddr *) result, &size);
          if (pton_ret != 0) { return 1; }
#else 
          int pton_ret = inet_pton(AF_INET6, address, addr->sin6_addr.s6_addr);
          if (pton_ret == 0) { return 1; }
#endif                  
                        
          addr->sin6_port = htons((short)port);
          *len = sizeof(*addr);
      } break;
    }
    return 0;
}
/**
 * Returns JS array with values describing remote address.
 * For UNIX socket, only one item is present. For AF_INET and
 * AF_INET6, array contains [address, port].
 * Returns v8::Undefined() on error.
 */
static v8::Handle<v8::Value> create_peer(sockaddr * addr)
{
    switch (addr->sa_family) {
#ifndef windows
      case AF_UNIX: {
          v8::Handle<v8::Array> result = v8::Array::New(1);
          sockaddr_un * addr_un = (sockaddr_un *) addr;
          result->Set( 0U, cv::CastToJS<char const *>(addr_un->sun_path));
          return result;
      } break;
#endif
      case AF_INET6: {
          v8::Handle<v8::Array> result = v8::Array::New(2);
          char buf[INET6_ADDRSTRLEN+1];
          memset( buf, 0, INET_ADDRSTRLEN+1 );
          sockaddr_in6 * addr_in6 = (sockaddr_in6 *) addr;

#ifdef windows
          DWORD len = INET6_ADDRSTRLEN;
          WSAAddressToString(addr, sizeof(struct sockaddr), NULL, buf, &len);
#else                   
          inet_ntop(AF_INET6, addr_in6->sin6_addr.s6_addr, buf, INET6_ADDRSTRLEN);
#endif
                        
          result->Set( 0U, cv::CastToJS(buf));
          result->Set( 1U, cv::CastToJS( ntohs(addr_in6->sin6_port)));
          return result;
      } break;
      case AF_INET: {
          v8::Handle<v8::Array> result = v8::Array::New(2);
          char buf[INET_ADDRSTRLEN+1];
          memset( buf, 0, INET_ADDRSTRLEN+1 );
          sockaddr_in * addr_in = (sockaddr_in *) addr;

#ifdef windows
          DWORD len = INET_ADDRSTRLEN;
          WSAAddressToString(addr, sizeof(struct sockaddr), NULL, buf, &len);
#else                   
          inet_ntop(AF_INET, & addr_in->sin_addr.s_addr, buf, INET_ADDRSTRLEN);
#endif
          result->Set( 0U, cv::CastToJS(buf));
          result->Set( 1U, cv::CastToJS(ntohs(addr_in->sin_port)));
          return result;
      } break;
    }
    return v8::Undefined();
}


void cv::JSSocket::init(int family, int type, int proto, int socketFD )
{
    this->family = family;
    this->proto = proto;
    this->type = type;
    if( socketFD < 0 )
    {
        this->fd = socket( family, type, proto );
    }
    else
    {
        this->fd = socketFD;
    }
    if( this->fd < 0 )
    {
        cv::StringBuffer msg;
        msg << "socket("<<family<<", "<<type<<", "<<proto<<") failed. errno="
                <<errno<<" ("<<::strerror(errno)<<").";
        throw std::runtime_error( msg.Content().c_str() );
    }
    { /* this idea comes from some code in Google v8 (platform-posix.cc, the POSIXSocket class)...*/
        static const int fastReUse = 1;
        int const rc = setsockopt(this->fd, SOL_SOCKET, SO_REUSEADDR, &fastReUse, sizeof(fastReUse));
        if( 0 != rc )
        {
            this->close();
            cv::StringBuffer msg;
            msg << "setsockopt() failed. errno="<<errno
                <<" ("<<::strerror(errno)<<").";
            throw std::runtime_error( msg.Content().c_str() );
        }
    }
}

cv::JSSocket::JSSocket(int family, int type, int proto, int socketFD )
    : fd(-1), family(0), proto(0),type(0),
      hitTimeout(false),
      pipeName(),
      jsSelf()
{
    this->init( family, type, proto, socketFD );
}

cv::JSSocket::~JSSocket()
{
    this->close();
}

void cv::JSSocket::close()
{
    if( this->fd >= 0 )
    {
        DBGOUT << "JSSocket@"<<(void const *)this<<"->close()\n";
        ::shutdown( this->fd, 2 );
        CloseSocket( this->fd );
        if( (AF_UNIX == this->family) && !this->pipeName.empty() )
        {
            std::remove( this->pipeName.c_str() );
            this->pipeName.clear();
        }
        this->fd = -1;
        
        
    }
}

int cv::JSSocket::bind( char const * where, int port )
{
    if( ! where || !*where )
    {
        Toss("Address argument may not be empty!");
        return -1;
    }
    sock_addr_t addr;
    socklen_t len = sizeof(sock_addr_t);
    memset( &addr, 0, len );
    int rc = 0;
    {
        CSignalSentry const sigSentry;
        v8::Unlocker const unl();
        rc = create_addr( where, port, this->family, &addr, &len );
    }
    cv::StringBuffer msg;
    if( 0 != rc )
    { // By-address failed, so we'll try by hostname...
        //CERR << "Bind to address "<<where<<" failed. Trying by name...\n";
        v8::Handle<v8::Value> const ip = nameToAddress( where );
        if( ! ip.IsEmpty() )
        {
            std::string const & ips = cv::JSToStdString(ip);
            CSignalSentry const sigSentry;
            v8::Unlocker const unl();
            rc = create_addr( ips.c_str(), port, this->family, &addr, &len );
        }
        if( 0 != rc )
        {
            msg << "Malformed address: ["<<where<<"] ";
        }
    }
    if( 0 == rc )
    {
        //CERR << "bind()ing...\n";
        {
            v8::Unlocker const unl;
            CSignalSentry const sigSentry;
            rc = ::bind( this->fd, (sockaddr *)&addr, len );
            if( (0 == rc) && (AF_UNIX == this->family) )
            {
                this->pipeName = ((struct sockaddr_un*) &addr)->sun_path;
            }
        }
        if( 0 != rc )
        {
            msg << "Bind failed! errno="<<errno<<" ("<<strerror(errno)<<")!";
        }
    }
    if( 0 != rc )
    {
        Toss( msg.toError() );
    }
    return rc;
}

int cv::JSSocket::listen( int backlog )
{
    int rc = -1;
    {
        v8::Unlocker const unlocker;
        CSignalSentry const sigSentry;
        rc = ::listen( this->fd, backlog );
    }
    // ^^^^ does socket timeout value apply here???
    if( 0 != rc )
    {
        cv::StringBuffer msg;
        msg << "listen() failed: errno="<<errno
            << " ("<<strerror(errno)<<')'
            ;
        Toss(msg.toError());
    }
    return rc;
}

int cv::JSSocket::listen()
{
    return this->listen( 5 );
}

int cv::JSSocket::getProtoByName( char const * name )
{
    struct protoent const * r = ::getprotobyname(name);
    return r ? r->p_proto : 0;
}

v8::Handle<v8::Value> cv::JSSocket::nameToAddress( char const * name, int family )
{
    if( ! name || !*name )
    {
        return Toss("'name' parameter may not be empty!");
    }
    struct addrinfo hints, * servinfo = NULL;
    memset(&hints, 0, sizeof(hints));
    hints.ai_family = family;
    int rc = 0;
    {
        v8::Unlocker unl;
        CSignalSentry const sigSentry;
        rc = getaddrinfo(name, NULL, &hints, &servinfo);
    }
    if (rc != 0)
    {
        cv::StringBuffer msg;
        msg << "getaddrinfo(\""<<name<<"\",...) failed: "<<gai_strerror(rc);
        return Toss(msg.toError());
    }
                
    v8::Handle<v8::Value> rv = create_peer(servinfo->ai_addr);
    freeaddrinfo(servinfo);
    if( rv.IsEmpty() ) return rv; // pass on exception
    v8::Local<v8::Object> item;
    if( rv->IsObject() )
    {
        item = rv->ToObject();
        return item->Get(cv::CastToJS<int>(0));
    }
    else
    {
        return v8::Undefined();
    }
}

v8::Handle<v8::Value> cv::JSSocket::nameToAddress( char const * name )
{
    return nameToAddress( name, 0 );
}

v8::Handle<v8::Value> cv::JSSocket::addressToName( char const * addy, int family )
{
    if( ! addy || !*addy )
    {
        return Toss("'address' parameter may not be empty!");
    }
    if( ! family ) family = AF_INET;
    char hn[NI_MAXHOST+1];
    memset( hn, 0, sizeof(hn) );
    sock_addr_t addr;
    socklen_t len = sizeof(sock_addr_t);
    memset( &addr, 0, len );
    //struct addrinfo hints; memset(&hints, 0, sizeof(hints));
    int rc = 0;
    {
        CSignalSentry const sigSentry;
        v8::Unlocker const unl();
        rc = create_addr( addy, 0, family, &addr, &len );
    }
    if( 0 != rc )
    {
        cv::StringBuffer msg;
        msg << "Malformed address: "<<addy;
        return Toss(msg.toError());
    }
    rc = ::getnameinfo( (sockaddr*) &addr, len, hn, NI_MAXHOST, NULL, 0, 0 );
    if( 0 != rc )
    {
        cv::StringBuffer msg;
        CSignalSentry const sigSentry;
        msg << "getnameinfo() failed with rc "<<rc <<
            " ("<<gai_strerror(rc)<<")";
        return Toss(msg.toError());
    }
    else
    {
        return cv::CastToJS(hn);
    }
}

v8::Handle<v8::Value> cv::JSSocket::addressToName( char const * addy )
{
    return addressToName( addy, 0 );
}


int cv::JSSocket::connect( char const * where, int port )
{
    if( ! where || !*where )
    {
        Toss("Address may not be empty!");
        return -1;
    }
    // FIXME: consolidate the duplicate code here and in bind():
    sock_addr_t addr;
    socklen_t len = sizeof(sock_addr_t);
    memset( &addr, 0, len );
    int rc = 0;
    {
        CSignalSentry sig;
        v8::Unlocker const unl();
        rc = create_addr(where, port, this->family, &addr, &len);
    }
    if( 0 != rc )
    {
        v8::Handle<v8::Value> ip = nameToAddress( where );
        if( ! ip.IsEmpty() )
        {
            std::string const & ips( cv::JSToStdString(ip) );
            v8::Unlocker const unl();
            rc = create_addr( ips.c_str(), port, this->family, &addr, &len );
        }
        if( 0 != rc )
        {
            cv::StringBuffer msg;
            msg << "Malformed address: "<<where;
            Toss(msg.toError());
            return rc;
        }
    }
    int errNo = 0;
    {
        v8::Unlocker unl;
        CSignalSentry const sigSentry;
        rc = ::connect( this->fd, (sockaddr *)&addr, len );
        errNo = errno;
    }
    if( 0 != rc )
    {
        cv::StringBuffer msg;
        msg << "connect() failed: errno="<<errNo
            << " ("<<strerror(errNo)<<')';
        Toss(msg.toError());
        return rc;
    }
    else
    {
        DBGOUT << "Connected to ["<<where<<':'<<port<<"]\n";
    }
    return 0;
}
    
int cv::JSSocket::connect( char const * addr )
{
    // TODO: do not require port # for AF_UNIX?
    return -1;
}

std::string cv::JSSocket::hostname()
{
    enum { MaxLen = 129 };
    char buf[MaxLen];
    int rc;
    memset( buf, 0, MaxLen );
    {
        v8::Unlocker const unl;
        CSignalSentry const sigSentry;
        rc = gethostname(buf, MaxLen-1 );
    }
    if( 0 != rc )
    {
        cv::StringBuffer msg;
        msg << "gethostname() failed: errno="<<errno
            << "( "<<strerror(errno)<<").";
        Toss(msg.toError());
        return std::string();
    }
    else
    {
        return buf;
    }
}

v8::Handle<v8::Value> cv::JSSocket::read( unsigned int n )
{
    return this->read( n, false );
}

unsigned int cv::JSSocket::write1( char const * src )
{
    return (src && *src)
        ? this->write2( src, strlen(src) )
        : 0
        ;
}

v8::Handle<v8::Value> cv::JSSocket::peerInfo()
{
    if( ! this->jsSelf->Get(JSTR(socket_strings.fieldPeer))->IsTrue() )
    {
        sock_addr_t addr;
        memset( &addr, 0, sizeof(sock_addr_t) );
        socklen_t len = sizeof(sock_addr_t);
        int rc = 0;
        {
            v8::Unlocker unl;
            rc = getpeername(this->fd, (sockaddr *) &addr, &len);
        }
        if (0 == rc)
        {
            this->jsSelf->Set(JSTR(socket_strings.fieldPeer), create_peer( (sockaddr*) &addr ) );
        }
        else
        {
            cv::StringBuffer msg;
            msg << "getpeername("<<this->fd<<",...) failed! errno="<<errno
                << " ("<<strerror(errno)<<")!";
            return Toss(msg.toError());
        }
    }
    return this->jsSelf->Get(JSTR(socket_strings.fieldPeer));
}

int cv::JSSocket::setOpt( int key, int val )
{
    int rc = setsockopt( this->fd, SOL_SOCKET, key, (void const *)&val, sizeof(int) );
    if( 0 != rc )
    {
        rc = errno;
        cv::StringBuffer msg;
        msg << "setsockopt("<<key<<", "<<val<<") failed! errno="<<errno
            << " ("<<strerror(errno)<<")"
            ;
        Toss(msg.toError());
    }
    return rc;
}

v8::Handle<v8::Value> cv::JSSocket::getOpt( int key )
{
    int buf = 0;
    socklen_t len = sizeof(buf);
    int rc = getsockopt( this->fd, SOL_SOCKET, key, (void *)&buf, &len );
    if( 0 != rc )
    {
        cv::StringBuffer msg;
        msg << "getsockopt("<<key<<") failed! errno="<<rc
            << " ("<<strerror(errno)<<")"
            ;
        return Toss(msg.toError());
    }
    else
    {
        return cv::CastToJS(buf);
    }
}


v8::Handle<v8::Value> cv::JSSocket::getOpt( int key, unsigned int len )
{
    typedef std::vector<char> VT;
    VT vec( len, '\0' );
    socklen_t slen = len;
    int rc = getsockopt( this->fd, SOL_SOCKET, key, (void *)&vec[0], &slen );
    if( 0 != rc )
    {
        cv::StringBuffer msg;
        msg << "getsockopt("<<key<<") failed! errno="<<rc
            << " ("<<strerror(errno)<<")"
            ;
        return Toss(msg.toError());
    }
    else
    {
        return cv::CastToJS(&vec[0]);
    }
}

int cv::JSSocket::setTimeout( unsigned int seconds, unsigned int usec )
{
    struct timeval t;
    t.tv_sec = seconds;
    t.tv_usec = usec;
    socklen_t len = sizeof(timeval);
    int rc = setsockopt( this->fd, SOL_SOCKET, SO_SNDTIMEO, &t, len );
    if( 0 == rc )
    {
        rc = setsockopt( this->fd, SOL_SOCKET, SO_RCVTIMEO, &t, len );
    }
    if( rc != 0 )
    {
        rc = errno;
    }
    return rc;
}

int cv::JSSocket::setTimeoutSec( unsigned int seconds )
{
    return this->setTimeout( seconds, 0 );
}

int cv::JSSocket::setTimeoutMs( unsigned int ms )
{
    unsigned const int sec = ms / 1000;
    unsigned const int usec = ms % 1000 * 1000;
    return this->setTimeout( sec, usec );
}


////////////////////////////////////////////////////////////////////////
// Set up our ClassCreator policies...
namespace cvv8 {
    
    v8::Handle<v8::Value> NativeToJS< JSSocket >::operator()( JSSocket * x ) const
    {
        if( x ) return x->jsSelf;
        else return v8::Null();
    }

    JSSocket * ClassCreator_Factory<JSSocket>::Create( v8::Handle<v8::Object> & jsSelf, v8::Arguments const & argv )
    {
        typedef cv::CtorForwarder< JSSocket * ()> Ctor0;
        typedef cv::CtorForwarder< JSSocket * (int)> Ctor1;
        typedef cv::CtorForwarder< JSSocket * (int,int)> Ctor2;
        typedef cv::CtorForwarder< JSSocket * (int,int,int)> Ctor3;
        typedef cv::CtorForwarder< JSSocket * (int,int,int,int)> Ctor4; // this one is only for internal use
        typedef cv::CtorArityDispatcher< cv::Signature< JSSocket *(
                Ctor0, Ctor1, Ctor2, Ctor3, Ctor4 
            )>
        > Dispatch;
        JSSocket * s = Dispatch::Call( argv );
        if( s )
        {
            s->jsSelf = jsSelf;
        }
        return s;
    }

    void ClassCreator_Factory<JSSocket>::Delete( JSSocket * obj )
    {
        obj->jsSelf = v8::Handle<v8::Object>();
        delete obj;
    }

} // v8::convert

/************************************************************************
   Down here is where the runtime setup parts of the bindings take place...
************************************************************************/

std::string cv::JSSocket::toString() const
{
    std::ostringstream os;
    os << "[object Socket@"<<(void const *)this
       << ']';
    return os.str();
}

v8::Handle<v8::Value> cv::JSSocket::sendTo( v8::Arguments const & argv )
{
    if( (argv.Length()<3) || (argv.Length()>4) )
    {
        return Toss("sendTo() requires 3-4 arguments!");
    }
    JSSocket * so = cv::CastFromJS<JSSocket>( argv.This() );
    if( ! so )
    {
        cv::StringBuffer msg;
        msg << "Could not find native 'this' argument for "
            << "socket object!";
        return Toss(msg.toError());
    }
    std::string where = cv::JSToStdString(argv[0]);
    int port = cv::JSToInt32(argv[1]);
    unsigned int len = 0;
    sock_addr_t addr;
    memset( &addr, 0, sizeof( sock_addr_t ) );
    socklen_t alen = 0;
    int rc = 0;
    {
        v8::Unlocker const unl();
        CSignalSentry sig;
        rc = create_addr(where.c_str(), port, so->family, &addr, &alen);
    }
    if( 0 != rc )
    {   // Connect using address failed. Try using a hostname...
        v8::Handle<v8::Value> ip = cv::JSSocket::nameToAddress( where.c_str() );
        if( ! ip.IsEmpty() )
        {
            where = cv::JSToStdString(ip);
            v8::Unlocker const unl();
            rc = create_addr( where.c_str(), port, so->family, &addr, &alen );
        }
        if( 0 != rc )
        {
            cv::StringBuffer msg;
            msg << "Malformed address(?): "<<where;
            return Toss(msg.toError());
        }
    }

    void const * buf = NULL;
    std::string sval;
    if( argv[2]->IsString() )
    {
        sval = cv::JSToStdString(argv[2]);
        if( argv.Length() > 3 )
        {
            len = cv::JSToUInt32(argv[3]);
            if( len > sval.size() ) len = sval.size();
        }
        else len = sval.size();
        buf = sval.c_str();
    }
    else
    {
        JSByteArray * ba = cv::CastFromJS<JSByteArray>( argv[2] );
        if( ! ba )
        {
            cv::StringBuffer msg;
            msg << "The second argument must be a String or ByteArray.";
            return Toss(msg.toError());
        }
        if( argv.Length() > 3 )
        {
            len = cv::JSToUInt32(argv[3]);
            if( len > ba->length() ) len = ba->length();
        }
        else len = ba->length();
        buf = ba->rawBuffer();
    }
    ssize_t sendToRC = -1;
    {
        v8::Unlocker unl;
        sendToRC = ::sendto( so->fd, buf, len, 0, (sockaddr *)&addr, alen );
    }
    if( -1 == sendToRC )
    {
        cv::StringBuffer msg;
        msg << "::sendto("<<so->fd<<"["<<where<<":"<<port<<"], <buffer>, "<<len<<",...) failed: errno="<<errno
            << " ("<<strerror(errno)<<")";
        return Toss( msg.toError() );
    }
    return cv::CastToJS( sendToRC );
}

v8::Handle<v8::Value> cv::JSSocket::writeN( v8::Arguments const & argv )
{
    if( argv.Length() > 2 )
    {
        return Toss("write() requires 1 or 2 arguments!");
    }
    JSSocket * so = cv::CastFromJS<JSSocket>( argv.This() );
    if( ! so )
    {
        cv::StringBuffer msg;
        msg << "Could not find native 'this' argument for socket object!";
        return Toss(msg.toError());
    }
    unsigned int len = 0;
    if( argv[0]->IsString() )
    {
        v8::String::Utf8Value const val(argv[0]);
        unsigned int const vlen = static_cast<unsigned int>(val.length());
        if( argv.Length() > 1 )
        {
            len = cv::JSToUInt32(argv[1]);
            if( len > vlen) len = vlen;
        }
        else len = vlen;
        return cv::CastToJS( so->write2( *val, len ) );
    }
    else
    {
        JSByteArray * ba = cv::CastFromJS<JSByteArray>( argv[0] );
        if( ! ba )
        {
            return Toss("The first argument must be a String or ByteArray.");
        }
        if( argv.Length() > 1 )
        {
            len = cv::JSToUInt32(argv[1]);
            if( len > ba->length() ) len = ba->length();
        }
        else len = ba->length();
        return cv::CastToJS( so->write2( (char const *)ba->rawBuffer(), len ) );
    }
}
unsigned int cv::JSSocket::write2( char const * src, unsigned int n )
{
    this->hitTimeout = false;
    ssize_t rc = 0;
    {
        v8::Unlocker const unl;
        CSignalSentry const sig;
        rc = ::write(this->fd, src, n );
        // reminder: ^^^^ affected by socket timeout. reminder: though
        // src technically comes from v8, it actually lives in a
        // std::string object (as a side-effect of the bindings' type
        // conversions, for the very reason of avoiding lifetime
        // issues) and therefore is not subject to v8 lifetime issues
        // during our Unlocker'd time. Or that's the theory.
    }
    if( (ssize_t)-1 == rc )
    {
        if( (EAGAIN==errno) || (EWOULDBLOCK==errno) )
        { /* Presumably(!) interrupted by a timeout. */
            this->hitTimeout = true;
            rc = 0;
        }
        else
        {
            cv::StringBuffer msg;
            msg << "socket write() failed! errno="<<errno
                << " ("<<strerror(errno)<<")";
            Toss( msg.toError() );
            rc = 0;
        }
    }
    return (unsigned int)rc;
}


v8::Handle<v8::Value> cv::JSSocket::read( unsigned int n, bool binary )
{
    this->hitTimeout = false;
    typedef std::vector<unsigned char> VT;
    VT vec(n,'\0');
    ssize_t rc = 0;
    sock_addr_t addr;
    socklen_t len = sizeof(sock_addr_t);
    memset( &addr, 0, len );
    {
        v8::Unlocker unl;
        CSignalSentry const sigSentry;
        DBGOUT << "read("<<n<<", "<<binary<<")...\n";
#if 1
        if(SOCK_DGRAM == this->type)
        { // UNTESTED!
#endif
            rc = ::recvfrom(this->fd, &vec[0], n, 0, (sockaddr *) &addr, &len);
#if 1
        }
        else
        {
            rc = ::read(this->fd, &vec[0], n);
        }
#endif
        DBGOUT << "read("<<n<<", "<<binary<<") == "<<rc<<"\n";
    }
    if( 0 == rc ) /*EOF*/ return v8::Undefined();
    if( (ssize_t)-1 == rc )
    {
#if 1
        if( (EAGAIN==errno) || (EWOULDBLOCK==errno) )
        { /* Presumably interrupted by a timeout. */
            this->hitTimeout = true;
            return v8::Null();
        }
#endif
        cv::StringBuffer msg;
        msg << "socket read() failed! errno="<<errno
            << " ("<<strerror(errno)<<")";
        return Toss( msg.toError() );
    }
    else
    {
#if 0
        if( (unsigned int) rc < n )
        {
            // dammit... we cannot distinguish timeout from EOF here....
            // this->hitTimeout = true;
        }
#endif
        if(SOCK_DGRAM == this->type)
        {
            // i'm not quite sure what this is for. It's from the original implementation.
            this->jsSelf->Set( JSTR(socket_strings.fieldPeer),
                               create_peer( (sockaddr*)&addr) );
        }
        vec.resize( rc );
        if( binary )
        {
            typedef cv::ClassCreator<JSByteArray> CW;
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
}

    
cv::JSSocket * cv::JSSocket::accept()
{
    int rc = 0;
    {
        v8::Unlocker unlocker;
        CSignalSentry const sigSentry;
        rc = ::accept( this->fd, NULL, NULL );
    }
    if( -1 == rc )
    {
        if( (errno == EAGAIN)
            || (errno == EWOULDBLOCK) )
        { /** presumably we would block for a non-blocking socket(?) */
            return NULL;
        }
        cv::StringBuffer msg;
        msg << "accept() failed: errno="<<errno
            << " ("<<strerror(errno)<<')';
        Toss(msg.toError());
        return NULL;
    }
    typedef cv::ClassCreator<JSSocket> CC;
    v8::Handle<v8::Value> argv[] =
        {
        cv::CastToJS( this->family ),
        cv::CastToJS( this->type ),
        cv::CastToJS( this->proto ),
        cv::CastToJS( rc )        
        };
    v8::Handle<v8::Object>
        const & jobj(CC::Instance().NewInstance( sizeof(argv)/sizeof(argv[0]), argv ));
    return cv::CastFromJS<JSSocket>( jobj );
}

void cv::JSSocket::SetupBindings( v8::Handle<v8::Object> const & dest )
{
    using namespace v8;
    HandleScope scope;
    typedef JSSocket N;
    typedef cv::ClassCreator<N> CC;
    CC & cc( CC::Instance() );
    DBGOUT <<"Binding socket class...\n";

    if( cc.IsSealed() )
    {
        cc.AddClassTo( "Socket", dest );
        return;
    }

    cc
        .Set( "close", CC::DestroyObjectCallback )
        ;

    typedef v8::Handle<v8::Value> ValH;
    typedef cv::MethodToInCa<N, ValH (unsigned int, bool), &N::read> Read2;
    typedef cv::MethodToInCa<N, ValH (unsigned int), &N::read> Read1;
#if 1
    typedef cv::ArityDispatch<2, Read2, cv::ArityDispatch<1,Read1> > OloadRead;
#else
    typedef cv::ArityDispatchList< Signature<void (Read2, Read1)> > OloadRead;
#endif
    cc.Set("read", OloadRead::Call);

    typedef cv::MethodToInCa<N, int (), &N::listen, false> Listen0;
    typedef cv::MethodToInCa<N, int (int), &N::listen, false> Listen1;
#if 1
    typedef cv::ArityDispatch<1, Listen1, cv::ArityDispatch<0,Listen0> > OloadListen;
#else
    typedef cv::ArityDispatchList< CVV8_TYPELIST((Listen0, Listen1)) > OloadListen;
#endif

    cc.Set("listen", OloadListen::Call);

    typedef cv::MethodToInCa<N, int (unsigned int, unsigned int), &N::setTimeout > SetTimeout2;
    typedef cv::MethodToInCa<N, int (unsigned int), &N::setTimeoutSec > SetTimeout1;
    typedef cv::ArityDispatch<2, SetTimeout2, cv::ArityDispatch<1,SetTimeout1> > OloadSetTimeout;
#define F2I cv::FunctionToInCa
#define M2I cv::MethodToInCa
#define C2I cv::ConstMethodToInCa
    
    cc("setTimeout", OloadSetTimeout::Call )
        ("setTimeoutMs", M2I<N, int (unsigned int),&N::setTimeoutMs, false>::Call )
        ( "close", CC::DestroyObjectCallback )
        ( "accept", M2I<N, JSSocket* (),&N::accept, false>::Call )
        ( "toString", C2I<N, std::string (),&N::toString>::Call )
        ( "bind", M2I<N,int (char const *,int),&N::bind,false>::Call )
        ( "connect", M2I<N,int (char const *, int), &N::connect, false>::Call )
        ( "nameToAddress", F2I< ValH (const char *), N::nameToAddress>::Call )
        ( "addressToName", F2I< ValH (const char *), N::addressToName>::Call )
        ( "write", cv::JSSocket::writeN )
        // is this useful? .Set( "sendTo", cv::JSSocket::sendTo )
        ( socket_strings.fieldPeer, false )
        ;
    v8::AccessorSetter const throwOnSet = ThrowingSetter::Set;
    v8::Handle<v8::ObjectTemplate> const & proto( cc.Prototype() );
    proto->SetAccessor( JSTR("family"), cv::MemberToGetter<N,int,&N::family>::Get, throwOnSet );
    proto->SetAccessor( JSTR("type"), cv::MemberToGetter<N,int,&N::type>::Get, throwOnSet );
    proto->SetAccessor( JSTR("timeoutReached"), cv::MemberToGetter<N,bool,&N::hitTimeout>::Get, throwOnSet );
    proto->SetAccessor( JSTR("peerInfo"), cv::MethodToGetter<N,ValH (),&N::peerInfo>::Get, throwOnSet );
    proto->SetAccessor( JSTR("hostname"), cv::FunctionToGetter<std::string (),&N::hostname>::Get, throwOnSet );

    v8::Handle<v8::Function> ctor = cc.CtorFunction();
    JSByteArray::SetupBindings( ctor );

#define SETInt(K) ctor->Set( JSTR(#K), v8::Integer::New(K) )
    SETInt(AF_INET);
    SETInt(AF_INET6);
    SETInt(AF_UNIX);
    SETInt(AF_UNSPEC);
    SETInt(SOCK_DGRAM);
    SETInt(SOCK_STREAM);
    SETInt(SOCK_SEQPACKET);
    SETInt(SOCK_RAW);
#undef SETInt

    ctor->Set( JSTR("hostname"), cv::CastToJS( N::hostname()), v8::ReadOnly );
    v8::InvocationCallback cb; cb = NULL;
#define JF v8::FunctionTemplate::New(cb)->GetFunction()
#define F(X) ctor->Set( JSTR(X), JF )

    cb = F2I< int (char const *), &N::getProtoByName >::Call;
    F("getProtoByName");

    typedef cv::FunctionToInCa<ValH (char const *), &N::nameToAddress> N2A1;
    typedef cv::FunctionToInCa<ValH (char const *,int), &N::nameToAddress> N2A2;
    typedef cv::ArityDispatch< 1, N2A1, cv::ArityDispatch< 2, N2A2 > > OloadN2A;
    cb = OloadN2A::Call;
    F("nameToAddress");

    typedef cv::FunctionToInCa<ValH (char const *), &N::nameToAddress> A2N1;
    typedef cv::FunctionToInCa<ValH (char const *,int), &N::nameToAddress> A2N2;
    typedef cv::ArityDispatch< 1, A2N1, cv::ArityDispatch< 2, A2N2 > > OloadA2N;
    cb = OloadA2N::Call;
    F("addressToName");

    cc.AddClassTo( "Socket", dest );
    DBGOUT <<"Binding done.\n";
#undef F2I
#undef M2I
#undef C2I
    return;
}

#undef CloseSocket
#undef DBGOUT
#undef JSTR
#undef USE_SIGNALS
#undef CERR
