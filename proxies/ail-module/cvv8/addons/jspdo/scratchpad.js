JSPDO.enableDebug = true;
var App = {
    db:new JSPDO('sqlite3::memory:')
};

function miniObjLayer() {
    print("scratchpad...\n");
    function createGetter(propName,inst) {
        return function() {
            return inst.$f[propName];
        };
    };
    function createSetter(propName,inst) {
        return function(val) {
            inst.$f[propName] = val;
            return this;
        };
    };

    function addAccessors(def, inst) {
        inst.$f = {};
        inst.get = {};
        inst.set = {};
        var k, f = def.fields;
        for( k in f ) {
            k = f[k];
            inst.get[k] = createGetter(k,inst);
            inst.set[k] = createSetter(k,inst);
            inst.$f[k] = null;
        }
    }

    function ObjProto(tableName)
    {
        this.table = tableName;
        return this;
    }
    
    ObjProto.prototype.toJSON = function() {
        return this.$f;
        return {
            table:this.table,
            fields:this.$f
        };
    };

    ObjProto.prototype.save = function(db) {
        db = db || this.$def.db;
        var st;
        try {
            var def = this.$def;
            var idField = def.fields[0];
            var k, ar = [];
            ar.push("UPDATE");
            ar.push(def.table);
            //ar.push( '('+def.fields.join(',')+')' );
            ar.push('SET');
            var qm = [];
            var binds = [];
            for( k in def.fields ) {
                k = def.fields[k];
                if( k === idField ) continue;
                qm.push(k+'=?');
                binds.push( this.$f[k] );
            }
            ar.push(qm.join(', '));
            qm = undefined;
            ar.push('WHERE '+idField+'=?');
            binds.push(this.$f[idField]);
            
            ar = ar.join(' ');
            print('SQL='+ar);

            st = db.prepare(ar);
            print("Prepared for UPDATE: "+JSON.stringify(st)+'\nBinds= '+JSON.stringify(binds));
            ar = undefined;
            st.bind(binds);
            st.step();
        }
        finally {
            if(st) st.finalize();
        }
    };
    
    ObjProto.prototype.createRecord = function(db) {
        db = db || this.$def.db;
        var st;
        try {
            var def = this.$def;
            var k, ar = [];
            ar.push("INSERT INTO");
            ar.push(def.table);
            ar.push( '('+def.fields.join(',')+')' );
            ar.push('VALUES(');
            var qm = [];
            for( k = 0; k < def.fields.length; ++k ) {
                qm.push('?');
            }
            ar.push(qm.join(','));
            qm = undefined;
            ar.push(')');
            ar = ar.join(' ');
            var binds = [];
            for( k in def.fields ) {
                k = def.fields[k];
                binds.push(this.$f[k]);
            }
            print('SQL='+ar);
            st = db.prepare(ar);
            print("Prepared for INSERT: "+JSON.stringify(st)+'\nBinds= '+JSON.stringify(binds));
            ar = undefined;
            st.bind(binds);
            binds = undefined;
            st.step();
            this.set[ def.fields[0] ]( db.lastInsertId(def.table) );
        }
        finally {
            if(st) st.finalize();
        }
    };

    var def = {
        db:null,
        table:"MyTable",
        fields:['id','name','parent'],
        relations:{
            "parent":{
                limit:1,
                table:"MyTable",
                field:"id"
            }
        },
        factory:function() {
            var o = new ObjProto(this.table);
            addAccessors(def,o);
            o.$def = this;
            return o;
        }
    };

    var db = App.db;
    def.db = db;
    try {
        db.exec("CREATE TABLE IF NOT EXISTS MyTable("+
        "id INTEGER PRIMARY KEY DEFAULT NULL, "+
        "name, "+
        "parent REFERENCES MyTable(id) DEFAULT NULL"+
        ")");

        var o = def.factory();
        o.createRecord();
        o.set.parent(0);
        print('id='+o.get.id()+', parent='+o.get.parent());
        print(JSON.stringify(o,0,4));
        o.set.name("Parent Object");
        JSPDO.enableDebug = true;
        o.save();
        print("saved(?): "+JSON.stringify(o));
        bob = def.factory();
        bob.set.parent(o.get.id());
        bob.set.name("Bob");
        bob.createRecord();
        print("created(?): "+JSON.stringify(bob));
        print('new id='+bob.get.id());
        print("Here's what we saved:");
        print(JSON.stringify( db.fetchAll({sql:"SELECT * FROM MyTable",mode:'object'}),0,4) );
    }
    catch(e) {
        print("EXCEPTION: "+e);
        throw e;
    }
    finally {
        //db.close();
    }

    print("End of scratchpad.");

};

try {
    miniObjLayer();
}
catch(e) {
    print("EXCEPTION: "+e);
}
finally {
    App.db.close();
    delete App.db;
};

