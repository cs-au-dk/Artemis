load('../test-common.js');
load('echo-config.inc.js');

function echoServer()
{
    var k,v;
    print("Socket members:");
    for( k in Socket )
    {
        print('\t'+k,'=',Socket[k]);
    }
    var s, c, n;
    try
    {
        s  = new Socket( echo.socketFamily, echo.socketType );
        print('s =',s);
        print('s.hostname =',s.hostname);
        var rc;
        var host, port;
        if( echo.socketFamily===Socket.AF_UNIX) {
            host = echo.socketPath;
            port = 0;
        } else {
            host = echo.host;
            port = echo.port;
        }
        var port = 
        assertThrows( function() {s.bind("",0);}, 'bind() throws for empty address.');
        rc = s.bind( host, echo.port );
        print( "s.bind("+host+(port ? (":"+port) : '')+") rc = "+rc);
        rc = s.setTimeout( 3 );
        print("s.setTimeout() rc =",rc);
        if( Socket.SOCK_STREAM == s.type )
        {
            print("Running in stream mode...");
            rc = s.listen();
            print("s.listen() rc =",rc);
            for( ; ; )
            {
                c = s.accept();
                print('accept =',c);
                if( ! c )
                {
                    print("Presuming a timeout and continuing...");
                    continue;
                }
                print("Got peer: "+c.peerInfo.join(':'));
                c.setTimeout( 10 );
                function doit(sock) {
                    var buf = new Socket.ByteArray();
                    var x;
                    var bufsz = 10;
                    var len;
                    while( undefined !== (x = sock.read(bufsz,true)) ) {
                        len = 0;
                        if( x ) {
                            len = x.length;
                            buf.append(x);
                            x.destroy();
                            print("Read in "+len+" bytes.");
                        }
                        //else { print("x = "+x); }
                        //if( sock.timeoutReached ) throw new Error("Timeout hit while reading request.");
                        if( null === x ) throw new Error("Timeout hit while reading request.");
                        else if(len < bufsz) break /* assume EOF */;
                        //else if(!len) break /* assume EOF */;
                        // else keep reading.
                    }
                    print("Writing back "+buf.length+" bytes to the client:\n"+buf+'\n'+buf.stringValue());
                    x = sock.write(buf);
                    buf.destroy();
                    print("Write rc="+x+". Closing client connection...");
                    sock.close();
                    print("Closed client connection.");
                };
                if(1) {
                    //setTimeout(function(){doit(c);},1);
                    doit(c);
                }
                continue;
            }
        }
        else if( Socket.SOCK_DGRAM == s.type )
        {
            var len = 5;
            // Is it normal tha i can only read a dgram socket 1 time?
            for( ; ; ) {
                print("Waiting on datagram read...");
                var buf = "";
                while( undefined !== (rc = s.read(len)) ) {
                    buf += rc;
                }
                if( buf.length > 0 ) {
                    print("s.read() rc =",rc,"Content=[\n"+buf+'\n]');
                }
            }
        }
        else
        {
            throw new Error("Unknown socket type!");
        }
    }
    catch(e) {
        print("EXCEPTION: "+e);
    }
    finally
    {
        print("Closing server socket...");
        if( s ) s.close();
        print("Closed server socket.");
    }
        
}

try
{
    //spawnIntervalThread(function(){print("tick...");},1000);
    echoServer();
    print("Done!");
}
catch(e)
{
    print("EXCEPTION:",e);
    throw e;
}
