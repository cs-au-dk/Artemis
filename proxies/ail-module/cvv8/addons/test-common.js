function printStackTrace(indention)
{
    var li = getStacktrace();
    if( li ) print('Stacktrace: '+JSON.stringify(li,0,indention));
}

function getCallLocation(framesBack){
    framesBack = (framesBack && (framesBack>0)) ? framesBack : 2;
    var li = getStacktrace(framesBack);
    if( !li ) return undefined;
    else return li[framesBack-1];
}


function assert(cond,msg)
{
    if( ! cond ) {
        var loc = getCallLocation(5);
        msg = 'Assertion failed in ['+loc.scriptName+
            '] at (or around) line '+
            loc.line+': '+
            (msg||'')+
            '\nStacktrace: '+JSON.stringify(getStacktrace(),0,4);
        throw new Error(msg);
    }
    else {
        print("Assertion OK: "+(msg || 'undescribed assertion'));
    }
}

function asserteq(got,expect,msg)
{
    msg = msg || (got+' == '+expect);
    if(1) {
        if( got != expect ) {
            var st = getStacktrace(2);
            var loc = st[1];
            msg = 'Assertion failed in ['+loc.scriptName+
                '] at (or around) line '+
                loc.line+': '+
                msg +
                '\nStacktrace: '+JSON.stringify(st,0,4);
            throw new Error(msg);
        }
        else print("Assertion OK: "+msg);
    }
    else {
        if( got != expect ) {
            throw new Error('Assertion failed: '+msg);
        }
        else print("Assertion OK: "+msg);
    }
        
}

function assertneq(got,expect,msg)
{
    msg = msg || (got+' != '+expect);
    if(1) {
        if( got == expect ) {
            var st = getStacktrace(2);
            var loc = st[1];
            msg = 'Assertion failed in ['+loc.scriptName+
                '] at (or around) line '+
                loc.line+': '+
                msg +
                '\nStacktrace: '+JSON.stringify(st,0,4);
            throw new Error(msg);
        }
        else print("Assertion OK: "+msg);
    }
    else {
        if( got == expect ) {
            throw new Error('Assertion failed: '+msg);
        }
        else print("Assertion OK: "+msg);
    }
        
}

/**
    Calls func(). If it throws, the assertion passes, else
    it fails. If msg is provided it is used as the assertion message,
    else some default message is used.
*/
function assertThrows( func, msg ) {
    var ex = undefined;
    msg = msg || "Got expected exception:";
    try { func(); }
    catch(e) { ex = e; }
    assert( !!ex, msg + ' '+ex );
    if(0) printStackTrace();
}
