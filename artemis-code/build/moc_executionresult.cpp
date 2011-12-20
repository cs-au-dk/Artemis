/****************************************************************************
** Meta object code from reading C++ file 'executionresult.h'
**
** Created: Tue Dec 20 14:39:04 2011
**      by: The Qt Meta Object Compiler version 63 (Qt 4.8.0)
**
** WARNING! All changes made in this file will be lost!
*****************************************************************************/

#include "../src/executionresult.h"
#if !defined(Q_MOC_OUTPUT_REVISION)
#error "The header file 'executionresult.h' doesn't include <QObject>."
#elif Q_MOC_OUTPUT_REVISION != 63
#error "This file was generated using the moc from 4.8.0. It"
#error "cannot be used with the include files from this version of Qt."
#error "(The moc has changed too much.)"
#endif

QT_BEGIN_MOC_NAMESPACE
static const uint qt_meta_data_artemis__ExecutionResult[] = {

 // content:
       6,       // revision
       0,       // classname
       0,    0, // classinfo
       5,   14, // methods
       0,    0, // properties
       0,    0, // enums/sets
       0,    0, // constructors
       0,       // flags
       0,       // signalCount

 // slots: signature, parameters, type, tag, flags
      36,   26,   25,   25, 0x0a,
      75,   26,   25,   25, 0x0a,
     143,  117,   25,   25, 0x0a,
     185,  181,   25,   25, 0x0a,
     199,   25,   25,   25, 0x0a,

       0        // eod
};

static const char qt_meta_stringdata_artemis__ExecutionResult[] = {
    "artemis::ExecutionResult\0\0elem,name\0"
    "newEventListener(QWebElement*,QString)\0"
    "removeEventListener(QWebElement*,QString)\0"
    "cause,sourceID,lineNumber\0"
    "sl_script_crash(QString,intptr_t,int)\0"
    "url\0add_url(QUrl)\0sl_eval_string(QString)\0"
};

void artemis::ExecutionResult::qt_static_metacall(QObject *_o, QMetaObject::Call _c, int _id, void **_a)
{
    if (_c == QMetaObject::InvokeMetaMethod) {
        Q_ASSERT(staticMetaObject.cast(_o));
        ExecutionResult *_t = static_cast<ExecutionResult *>(_o);
        switch (_id) {
        case 0: _t->newEventListener((*reinterpret_cast< QWebElement*(*)>(_a[1])),(*reinterpret_cast< QString(*)>(_a[2]))); break;
        case 1: _t->removeEventListener((*reinterpret_cast< QWebElement*(*)>(_a[1])),(*reinterpret_cast< QString(*)>(_a[2]))); break;
        case 2: _t->sl_script_crash((*reinterpret_cast< QString(*)>(_a[1])),(*reinterpret_cast< intptr_t(*)>(_a[2])),(*reinterpret_cast< int(*)>(_a[3]))); break;
        case 3: _t->add_url((*reinterpret_cast< const QUrl(*)>(_a[1]))); break;
        case 4: _t->sl_eval_string((*reinterpret_cast< const QString(*)>(_a[1]))); break;
        default: ;
        }
    }
}

const QMetaObjectExtraData artemis::ExecutionResult::staticMetaObjectExtraData = {
    0,  qt_static_metacall 
};

const QMetaObject artemis::ExecutionResult::staticMetaObject = {
    { &QObject::staticMetaObject, qt_meta_stringdata_artemis__ExecutionResult,
      qt_meta_data_artemis__ExecutionResult, &staticMetaObjectExtraData }
};

#ifdef Q_NO_DATA_RELOCATION
const QMetaObject &artemis::ExecutionResult::getStaticMetaObject() { return staticMetaObject; }
#endif //Q_NO_DATA_RELOCATION

const QMetaObject *artemis::ExecutionResult::metaObject() const
{
    return QObject::d_ptr->metaObject ? QObject::d_ptr->metaObject : &staticMetaObject;
}

void *artemis::ExecutionResult::qt_metacast(const char *_clname)
{
    if (!_clname) return 0;
    if (!strcmp(_clname, qt_meta_stringdata_artemis__ExecutionResult))
        return static_cast<void*>(const_cast< ExecutionResult*>(this));
    return QObject::qt_metacast(_clname);
}

int artemis::ExecutionResult::qt_metacall(QMetaObject::Call _c, int _id, void **_a)
{
    _id = QObject::qt_metacall(_c, _id, _a);
    if (_id < 0)
        return _id;
    if (_c == QMetaObject::InvokeMetaMethod) {
        if (_id < 5)
            qt_static_metacall(this, _c, _id, _a);
        _id -= 5;
    }
    return _id;
}
QT_END_MOC_NAMESPACE
