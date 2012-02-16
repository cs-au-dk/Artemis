var echo = {
host:'127.0.0.1',
//port:9090,
port:8081,
socketPath:'/tmp/v8socket.sock',
crnl:'\r\n'
};
echo.socketType =
    //echo.Socket.SOCK_DGRAM
    Socket.SOCK_STREAM
    ;
//echo.socketFamily = Socket.AF_UNIX;
echo.socketFamily = Socket.AF_INET;

/**
    Reminder to self:
    
    when using Socket.AF_UNIX we can do the following:
    
    sock.bind('/path/to/socket',0);
    
    then:
    
    netcat -U /path/to/socket < /etc/hosts
    
    However:
    
    The socket file is not deleted when the socket is closed :/, which
    causes an "Address in use" error the next time we try to bind()
    to it.
*/
