print("Starting tests...");

load('../test-common.js');

//JSPDO.enableDebug = true;
//JSPDO.ByteArray.enableDestructorDebug(true);
//JSPDO.enableDestructorDebug(true);
var App = {
    drv:null,
    user:"",
    password:"",
    tableName:'mytbl',
    CREATE:{
        mysql5:"CREATE TABLE IF NOT EXISTS mytbl("+
                 "id INTEGER PRIMARY KEY NOT NULL AUTO_INCREMENT, "+
                 "a INTEGER DEFAULT NULL,"+
                 "b DOUBLE DEFAULT NULL,"+
                 "c VARCHAR(127) DEFAULT NULL, "+
                 "d BLOB DEFAULT NULL"+
                 ")",
        sqlite3:"CREATE TABLE IF NOT EXISTS mytbl("+
                 "id INTEGER PRIMARY KEY DEFAULT NULL,"+
                 "a INTEGER DEFAULT NULL,"+
                 "b DOUBLE DEFAULT NULL,"+
                 "c VARCHAR(127) DEFAULT NULL, "+
                 "d BLOB DEFAULT NULL"+
                 ")"
    }
};
if(1) { // sqlite3 ...
    App.dsn = 'sqlite3::memory:';
}
else { // MySQL...
    App.dsn = 'mysql5:host=localhost;dbname=cpdo';
    App.user = App.password = 'cpdo';
}

function testConnect() {
    var drv = App.drv = new JSPDO(App.dsn,App.user,App.password);
    print("Driver: "+JSON.stringify(drv,0,4));
    print('JSPDO.columnTypes: '+JSON.stringify(JSPDO.columnTypes,0,4));
    print("Available db drivers: "+JSON.stringify(JSPDO.driverList));
    assertThrows(function() { drv.driverName = "should throw"; });
    asserteq( true, !!App.CREATE[drv.driverName] );
    drv.exec(App.CREATE[drv.driverName]);
    drv.exec("DELETE FROM "+App.tableName);
}

function testSelect(mode)
{
    var drv = App.drv;
    var st;
    var sql = "select id as id, a as a,b as b,c as c, d as d from "+App.tableName;
    try {
        st = drv.prepare(sql);
    }
    catch(e) {
        print("Error preparing sql. Db says: Code #"+drv.errorCode+": "+drv.errorText);
        return;
    }
    print('Testing SELECT. statement='+JSON.stringify(st));
    var sep = '\t';
    if( !st ) throw new Error("WTF? st is null?");
    var colCount = st.columnCount;
    print("Column count="+colCount);
    try {
        assertThrows(function(){st.columnNames="should throw";});
        var rowCount = 0, i;
        if('object'===mode) {
            var row;
            while( (row = st.stepObject()) ) {
                //asserteq( colCount, row.length, 'Column count matches.' );
                print(JSON.stringify(row));
                ++rowCount;
            }
        }
        else if('array'===mode){
            print( st.columnNames.join(sep) );
            var row;
            while( (row = st.stepArray()) ) {
                //asserteq( colCount, row.length, 'Column count matches.' );
                print(row.join(sep));
                ++rowCount;
            }
        }
        else {
            print( st.columnNames.join(sep) );
            var cols = [], v;
            while( st.step() ) {
                ++rowCount;
                cols.length = 0;
                for(i=0; i < colCount;++i ) {
                    v = st.get(i);
                    cols.push('[type='+st.columnType(i)+']'+
                              ( (v===null) ? 'NULL' : v )
                              );
                }
                print(cols.join(sep));
            }
        }
        print(rowCount+" row(s)");
    }
    finally {
        st.finalize();
    }

}

function testCleanup()
{
    App.drv.exec("DELETE FROM "+App.tableName);
}

function testInsert()
{
    var st;
    try {
        var sql = "INSERT INTO "+App.tableName+"(a,b,c,d) VALUES(?,?,?,?)";
        var ds = (new Date()).toString();
        st = App.drv.prepare(sql);
        print("Inserting: "+st);
        st.bind(1);
        st.bind(2,24.42);
        st.bind(3, ds);
        var d = new JSPDO.ByteArray("this is a ByteArray");
        st.bind(4, d);
        d.destroy();
        //assertThrows( function() { st.bind(4); } );
        st.step();
        print('Inserted new record. ID='+App.drv.lastInsertId("ignored"));
        st.reset();
        st.bind([42, 42.24, null]);
        st.step();
        print('Inserted new record. ID='+App.drv.lastInsertId());
        print('SQL = '+st.sql);
    }
    finally {
        if( st ) {
            st.finalize();
        }
    }
}

function testInsertNamedParams() {
    var st;
    try {
        var sql = "INSERT INTO "+App.tableName+"(a,b,c,d) VALUES(:pA,:pB,:pC,:pD)";
        var ds = (new Date()).toString();
        st = App.drv.prepare(sql);
        asserteq(3,st.paramIndex(':pC'));
        asserteq(0,st.paramIndex(':pX'));
        st.bind(':pB', 32.23);
        var d = new JSPDO.ByteArray("this is a ByteArray");
        st.bind({pA:7, ':pC':ds, pD:d});
        d.destroy();
        print("Inserting: "+st);
        print('Parameter names: '+JSON.stringify(st.paramNames));
        assertThrows(function(){st.paramNames="should throw";});
        assertThrows( function() { st.bind(':pX'); } );
        st.step();
        print('Inserted new record using named params. ID='+App.drv.lastInsertId());
    }
    finally {
        if( st ) {
            st.finalize();
        }
    }

}

function testExt_forEach() {
    var sql = "SELECT * FROM "+App.tableName+" WHERE a IS NOT NULL LIMIT 3";
    var st = App.drv.prepare(sql);
    var opt = {
        sql:st,
        //bind:[20],
        //bind:function(st){st.bind(1,20)},
        mode:'object',
        //mode:'array',
        each:function(row,data){
            ++data.rows;
            print(JSON.stringify(row));
        },
        callbackData:{rows:0}
    };
    print("Trying db.exec("+JSON.stringify(opt)+")");
    JSPDO.enableDestructorDebug(true);
    try {
        App.drv.exec(opt);
        
    }
    finally {
        //if( sql instanceof JSPDO.Statement ) sql.finalize();
        //asserteq( false, sql.finalize(), 'sql was finalized by exec()');
        //WTF? finalize() is returning undefined instead of bool???
        JSPDO.enableDestructorDebug(false);
    }
    asserteq( 2, opt.callbackData.rows, 'expecting 2 rows' );
    print(opt.callbackData.rows+" row(s)");
}

function testExt_fetchAll() {
    var sql;
    sql = "SELECT * FROM "+App.tableName+" WHERE a > :pA LIMIT 3";
    if(1) {
        sql = App.drv.prepare(sql);
        print('fetchAll() parameter names: '+JSON.stringify(sql.paramNames));
        print('parameter name 1: '+sql.paramName(1));
        assertThrows( function() { sql.paramName(5) } );
    }
    var opt = {
        sql:sql,
        bind:{pA:5},
        mode:'array'
        //mode:'object'
    };
    print("Trying db.fetchAll( "+JSON.stringify(opt)+" )");
    var all;
    try {
        all = App.drv.fetchAll(opt);
    }
    finally {
        if( sql instanceof JSPDO.Statement ) sql.finalize();
    }
    print(JSON.stringify(all));
    print(all.rows.length+" row(s)");
    asserteq( 2, all.rows.length, 'expecting 2 rows' );
}

function testCopyDb() {
    var db1 = App.drv;
    var db2, st1, st2;
    try {
        db2 = new JSPDO('sqlite3::memory:');
        print("Copying "+App.tableName+".* from "+db1+" to "+db2+"...");
        db2.exec(App.CREATE[db2.driverName]);
        db2.exec("DELETE FROM "+App.tableName);
        st1 = db1.prepare("SELECT * FROM "+App.tableName);
        var i, f = new Array(st1.columnCount);
        for( i = 0; i < f.length; ++i ) f[i] = '?';
        st2 = db2.prepare("INSERT INTO "+App.tableName+" ("+
                        st1.columnNames.join(',')+
                        ') VALUES('+f.join(',')+')');
        f = null;
        i = 0;
        db2.begin();
        while( st1.step() ) {
            st2.bind(st1);
            st2.step();
            st2.reset();
            ++i;
        }
        st1.finalize(); st1 = null;
        st2.finalize(); st2 = null;
        db2.commit();
        print("Copied "+i+" record(s) to second db instance. Results:");
        db2.exec({
            sql:"SELECT * FROM "+App.tableName,
            each:function(row) {print(JSON.stringify(row));},
            mode:'array'
        });
    }
    finally {
        if( st1 ) st1.finalize();
        if( st2 ) st2.finalize();
        if( db2 ) db2.close();
    }
}

function testUnclosedHandles() {
    var count = 3;
    var db = new JSPDO('sqlite3::memory:');
    print("Testing closing of danging statement handles...");
    try {
        for( var i = 0; i < count; ++i ) {
            var st = db.prepare("SELECT COUNT(*) FROM sqlite_master");
            //st.step();
            print('Intentionally trying to "leak" statement '+st);
        }
    }
    finally {
        print("If JSPDO.enableDebug is on you should see several Statement dtors...");
        print("At the very least, it shouldn't crash during GC as a result of these leaked statements.");
        db.close();
    }
}

function testGzippedJSON()
{
    var db = App.drv;
    db.exec("DROP TABLE IF EXISTS ziptest");
    db.exec("CREATE TABLE ziptest(name VARCHAR(50) NOT NULL, json BLOB DEFAULT NULL)");
    var theObj = { // an object to store in the DB as compressed JSON
        a:"Äaöoüu",
        b:42,
        db:db.toJSON(),
        list:[]
    };
    // Add some filler so that the data can actually compress a bit...
    var i;
    for( i = 1; i <= 10; ++i ) { theObj.list.push("Line #"+i+"\n"); };
    var json = JSON.stringify(theObj,0,4);
    // Stuff it into the database...
    var st;    
    try {
        var bac, ba, compressedSize;
        print("Inserting compressed data....");
        st = db.prepare("INSERT INTO ziptest (name,json) VALUES (?,?)");
        st.bind(1,"bogo");
        ba = new JSPDO.ByteArray( json );
        bac = ba.gzip();
        ba.destroy();
        st.bind(2,bac);
        compressedSize = bac.length;
        bac.destroy();
        st.step();
        print("Inserted compressed data.");
        st.finalize();
        st = null;
        // Now read it back and compare it ot the original...
        var cbData = {rows:0};
        db.exec({
            sql:"SELECT name as name,json as json FROM ziptest",
            callbackData:cbData,
            each:function(st,data) {
                ++data.rows;
                var ba = st.get(1);
                assert(ba instanceof JSPDO.ByteArray,'Field is-a ByteArray');
                print("Got compressed field data: "+ba);
                var buc = ba.gunzip();
                ba.destroy();
                var sv = buc.stringValue();
                print("Uncompressed JSON data: "+buc+" Length: "+
                    buc.length+" bytes/"+sv.length+' UTF8 characters');
                buc.destroy();
                assert( sv === json, "Decompressed JSON matches original" );
            }
        });
        asserteq( 1, cbData.rows, "Row count is 1." );
        var sizeSQL = "SELECT name, LENGTH(json) FROM ziptest";
        db.exec({
            sql:sizeSQL,
            callbackData:cbData,
            each:function(st,data) {
                cbData.dataLength = st.get(1);
            }
        });
        asserteq( compressedSize, cbData.dataLength, 'Db-side and JS-side blob sizes match');
        asserteq( db.selectValue({sql:sizeSQL,column:1}), cbData.dataLength, 'db.selectValue() agrees on the size.' );
    }
    finally {
        if(st) st.finalize();
    }
}

try {
    testConnect();
    testCleanup();
    assert( App.drv, "Driver is alive." );
    testSelect();
    testInsert();
    testSelect('object');
    testInsertNamedParams();
    testSelect('array');
    testSelect();
    testExt_forEach();
    testExt_fetchAll();
    testCopyDb();
    testGzippedJSON();
    if( 1 ) {
        testUnclosedHandles();
    }
}
catch(e) {
    print("GOT AN EXCEPTION: "+e);
    //stacktrace is reset in catch! print("Stacktrace:\n"+JSON.stringify(getStacktrace(),0,4));
    throw e;
}
finally {
    if( App.drv ) {
        print("Closing driver connection "+JSON.stringify(App.drv));
        App.drv.close();
        delete App.drv;
    }
}

print("Tests finished.");
