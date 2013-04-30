/**
    A JSPDO demo app which connects to a whiki database.

    http://whiki.wanderinghorse.net

    Far from complete!

    This client requires a direct connection to the whiki db, as opposed to
    running over the web API (we don't yet have a libcurl wrapper for cvv8).

    Usage:

      jspdo THIS_FILE.js -- --dsn=jspdo_dsn [--user=...] [--password=...] COMMAND CMD_ARGS

    --user and --password are only need for MySQL DSNs.

    Currently implemented commands:

        list (or ls): a list of whiki page objects, minus content and clientData
        fields.

        content PAGENAME: dumps just the content of the given page to stdout

    TODO:

    Options:

        -c=configfile.json, to store e.g. DSN.

    Commands:
    
        import PAGENAME [ContentType]: imports a file into a page. Need
        input routine for that, of course.
*/

function Whiki(dsn,user,password)
{
    this.db = new JSPDO(dsn,user,password);
    this.cache = {};
    this.opt = {
        tablePrefix:'whiki_'
    };
    return this;
}

Whiki.parseArgs = function(args) {
    var i, m, l;
    var rxNonFlag = /^[^-][^=]+?$/; /* -arg */
    var rx0a = /^--?([^=]+)$/; /* -[-]arg */
    var rx1a = /^--?([^=]+)=(.*)$/; /* -[-]arg=val */
    var rc = {
        flags:{},
        nonFlags:[]
    };
    for( i = 0; i < args.length; ++i ) {
        l = args[i];
        //print("TRYING ["+i+"]="+l);
        if( ! l ) continue;
        else if( rxNonFlag.test(l) ) {
            rc.nonFlags.push(l);
        }
        else if( (m = rx0a.exec(l)) ) {
            rc.flags[ m[1] ] = true;
        }
        else if( (m = rx1a.exec(l)) ) {
            rc.flags[ m[1] ] = (m[2] || false);
        }
        else {
            // ??? wtf ???
        }
    }
    return rc;
};

Whiki.enableDebug = false;
Whiki.debug = function() {
    if( this.enableDebug ) print.apply( this, Array.prototype.slice.apply( arguments, [0]) );
};

Whiki.prototype.expandTableName = function(t) {
    return this.opt.tablePrefix+t;
};

Whiki.prototype.buildPageMap = function() {
    if( ! this.cache.pageList ) {
        throw new Error("buildPageMap() must not be called until the page list is loaded.");
    }
    var i, v;
    var m = this.cache.pages = {};
    for( i = 0; i < this.cache.pageList.length; ++i ) {
        v = this.cache.pageList[i];
        m[v.name] = v;
    }
};

Whiki.prototype.loadPageList = function(forceReload) {
    if( this.cache.pageList && !forceReload ) return this.cache.pageList;
    var sql = "SELECT name as name, ctype as contentType, lastsaved as lastSaved "+
                "FROM "+this.expandTableName('page')+' ORDER BY name';
    var res = this.db.fetchAll({sql:sql,mode:'object'});
    this.cache.pageList = res.rows;
    this.buildPageMap();
    return res.rows;
};
Whiki.prototype.normalizePageParam = function(p) {
    if( ! p ) return false;
    else if( !this.cache.pages ) return false;
    else if( 'string' === typeof p ) return this.cache.pages[p];
    else return p;
}
Whiki.prototype.loadPageContent = function(p) {
    p = this.normalizePageParam(p);
    if( !p || !this.cache.pages[p.name] ) {
        throw new Error("loadPageContent() must not be called until the page list is loaded.");
    }
    if(undefined!==p.content) return p;
    var name = p.name;
    var c = this.db.selectValue({
        sql:"SELECT content FROM "+this.expandTableName('page')+
            " WHERE name=?",
        bind:[name]
    });
    if( c instanceof JSPDO.ByteArray ) {
        var x = c;
        c = x.stringValue();
        x.destroy();
    }
    p.content = c;
    return p;
};
Whiki.prototype.getPage = function(name) {
    this.loadPageList();
    var p = this.cache.pages[name];
    if( ! p ) throw new Error("Unkown page ["+name+"]");
    if( undefined!==p.content ) return p;
    return this.loadPageContent(p);
};


var App = {};

App.listPages = function(list) {
    var pl = this.w.loadPageList();
    print(JSON.stringify(pl,0,4));
};

App.dumpPageContent = function(list) {
    //Whiki.debug(JSON.stringify(list,0,4));
    var i, v;
    if( ! list.length ) {
        throw new Error("No page name(s) provided.");
    }
    for( i = 0; i < list.length; ++i ) {
        v = this.w.getPage(list[i]);
        print(v.content);
    }
    
};

App.dispatchCommand = function(opt)
{
    if( !opt.nonFlags || !opt.nonFlags.length ) {
        throw new Error("No command specified.");
    }
    this.cliOpt = opt;
    var li = JSON.parse(JSON.stringify(opt.nonFlags));
    var cmd = li[0];
    li.shift();
    var cmdArgs = li;
    var map = {
        list:'listPages',
        ls:'listPages',
        content:'dumpPageContent'
    };
    //Whiki.debug("cmdArgs="+JSON.stringify(cmdArgs));
    var fname = map[cmd];
    if( ! fname ) {
        throw new Error("Unknown command '"+cmd+"'. Please RTFSrc.");
    }
    var func = this[fname];
    if( 'function' !== typeof func ) {
        throw new Error("Internal error: function '"+fname+"' not found!");
    }
    func.call(this,cmdArgs);
};

App.main = function(opt)
{
    var fl = opt.flags
    Whiki.debug("CLI args: "+JSON.stringify(opt));
    if( ! fl ) {
        throw new Error("No arguments specified!");
    }
    if( ! fl.dsn ) {
        throw new Error("Required option --dsn is missing.");
    }
    this.w = new Whiki(fl.dsn,fl.user,fl.password);
    try {
        this.w.loadPageList();
        this.dispatchCommand(opt);
    }
    catch(e) {
        print("ERROR: "+e);
    }
    finally {
        Whiki.debug("Closing "+App.w.db);
        this.w.db.close();
        delete this.w.db;
    }
};

if( arguments && arguments.length ) {
    arguments.parsed = Whiki.parseArgs(arguments);
    App.main( arguments.parsed );
    //print(JSPDO.readFileContents('whiki-local.js'));
    //print(JSPDO.readFileContents('whiki-local.js',true));
}
