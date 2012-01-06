/****************************************************************************
** Meta object code from reading C++ file 'webkitexecutor.h'
**
** Created: Tue Jan 3 22:46:14 2012
**      by: The Qt Meta Object Compiler version 63 (Qt 4.8.0)
**
** WARNING! All changes made in this file will be lost!
*****************************************************************************/

#include "../src/webkitexecutor.h"
#if !defined(Q_MOC_OUTPUT_REVISION)
#error "The header file 'webkitexecutor.h' doesn't include <QObject>."
#elif Q_MOC_OUTPUT_REVISION != 63
#error "This file was generated using the moc from 4.8.0. It"
#error "cannot be used with the include files from this version of Qt."
#error "(The moc has changed too much.)"
#endif

QT_BEGIN_MOC_NAMESPACE
static const uint qt_meta_data_artemis__WebKitExecutor[] = {

 // content:
       6,       // revision
       0,       // classname
       0,    0, // classinfo
       6,   14, // methods
       0,    0, // properties
       0,    0, // enums/sets
       0,    0, // constructors
       0,       // flags
       1,       // signalCount

 // signals: signature, parameters, type, tag, flags
      34,   25,   24,   24, 0x05,

 // slots: signature, parameters, type, tag, flags
      98,   95,   24,   24, 0x0a,
     122,  119,   24,   24, 0x0a,
     171,  160,   24,   24, 0x0a,
     211,  201,   24,   24, 0x0a,
     239,  235,   24,   24, 0x0a,

       0        // eod
};

static const char qt_meta_stringdata_artemis__WebKitExecutor[] = {
    "artemis::WebKitExecutor\0\0conf,res\0"
    "sigExecutedSequence(ExecutableConfiguration,ExecutionResult)\0"
    "ok\0slloadFinished(bool)\0,,\0"
    "sl_script_crash(QString,intptr_t,int)\0"
    ",post_data\0sl_ajax_request(QUrl,QString)\0"
    "eval_text\0sl_eval_called(QString)\0,,,\0"
    "sl_code_loaded(intptr_t,QString,QUrl,int)\0"
};

void artemis::WebKitExecutor::qt_static_metacall(QObject *_o, QMetaObject::Call _c, int _id, void **_a)
{
    if (_c == QMetaObject::InvokeMetaMethod) {
        Q_ASSERT(staticMetaObject.cast(_o));
        WebKitExecutor *_t = static_cast<WebKitExecutor *>(_o);
        switch (_id) {
        case 0: _t->sigExecutedSequence((*reinterpret_cast< ExecutableConfiguration(*)>(_a[1])),(*reinterpret_cast< ExecutionResult(*)>(_a[2]))); break;
        case 1: _t->slloadFinished((*reinterpret_cast< bool(*)>(_a[1]))); break;
        case 2: _t->sl_script_crash((*reinterpret_cast< QString(*)>(_a[1])),(*reinterpret_cast< intptr_t(*)>(_a[2])),(*reinterpret_cast< int(*)>(_a[3]))); break;
        case 3: _t->sl_ajax_request((*reinterpret_cast< QUrl(*)>(_a[1])),(*reinterpret_cast< QString(*)>(_a[2]))); break;
        case 4: _t->sl_eval_called((*reinterpret_cast< QString(*)>(_a[1]))); break;
        case 5: _t->sl_code_loaded((*reinterpret_cast< intptr_t(*)>(_a[1])),(*reinterpret_cast< QString(*)>(_a[2])),(*reinterpret_cast< QUrl(*)>(_a[3])),(*reinterpret_cast< int(*)>(_a[4]))); break;
        default: ;
        }
    }
}

const QMetaObjectExtraData artemis::WebKitExecutor::staticMetaObjectExtraData = {
    0,  qt_static_metacall 
};

const QMetaObject artemis::WebKitExecutor::staticMetaObject = {
    { &QObject::staticMetaObject, qt_meta_stringdata_artemis__WebKitExecutor,
      qt_meta_data_artemis__WebKitExecutor, &staticMetaObjectExtraData }
};

#ifdef Q_NO_DATA_RELOCATION
const QMetaObject &artemis::WebKitExecutor::getStaticMetaObject() { return staticMetaObject; }
#endif //Q_NO_DATA_RELOCATION

const QMetaObject *artemis::WebKitExecutor::metaObject() const
{
    return QObject::d_ptr->metaObject ? QObject::d_ptr->metaObject : &staticMetaObject;
}

void *artemis::WebKitExecutor::qt_metacast(const char *_clname)
{
    if (!_clname) return 0;
    if (!strcmp(_clname, qt_meta_stringdata_artemis__WebKitExecutor))
        return static_cast<void*>(const_cast< WebKitExecutor*>(this));
    return QObject::qt_metacast(_clname);
}

int artemis::WebKitExecutor::qt_metacall(QMetaObject::Call _c, int _id, void **_a)
{
    _id = QObject::qt_metacall(_c, _id, _a);
    if (_id < 0)
        return _id;
    if (_c == QMetaObject::InvokeMetaMethod) {
        if (_id < 6)
            qt_static_metacall(this, _c, _id, _a);
        _id -= 6;
    }
    return _id;
}

// SIGNAL 0
void artemis::WebKitExecutor::sigExecutedSequence(ExecutableConfiguration _t1, ExecutionResult _t2)
{
    void *_a[] = { 0, const_cast<void*>(reinterpret_cast<const void*>(&_t1)), const_cast<void*>(reinterpret_cast<const void*>(&_t2)) };
    QMetaObject::activate(this, &staticMetaObject, 0, _a);
}
QT_END_MOC_NAMESPACE
