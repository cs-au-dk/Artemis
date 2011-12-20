/****************************************************************************
** Meta object code from reading C++ file 'coveragelistener.h'
**
** Created: Tue Dec 20 14:39:12 2011
**      by: The Qt Meta Object Compiler version 63 (Qt 4.8.0)
**
** WARNING! All changes made in this file will be lost!
*****************************************************************************/

#include "../src/coverage/coveragelistener.h"
#if !defined(Q_MOC_OUTPUT_REVISION)
#error "The header file 'coveragelistener.h' doesn't include <QObject>."
#elif Q_MOC_OUTPUT_REVISION != 63
#error "This file was generated using the moc from 4.8.0. It"
#error "cannot be used with the include files from this version of Qt."
#error "(The moc has changed too much.)"
#endif

QT_BEGIN_MOC_NAMESPACE
static const uint qt_meta_data_artemis__CoverageListener[] = {

 // content:
       6,       // revision
       0,       // classname
       0,    0, // classinfo
       2,   14, // methods
       0,    0, // properties
       0,    0, // enums/sets
       0,    0, // constructors
       0,       // flags
       0,       // signalCount

 // slots: signature, parameters, type, tag, flags
      51,   27,   26,   26, 0x0a,
     121,   87,   26,   26, 0x0a,

       0        // eod
};

static const char qt_meta_stringdata_artemis__CoverageListener[] = {
    "artemis::CoverageListener\0\0"
    "id,source,url,startline\0"
    "new_code(intptr_t,QString,QUrl,int)\0"
    "sourceID,function_name,linenumber\0"
    "statement_executed(intptr_t,std::string,int)\0"
};

void artemis::CoverageListener::qt_static_metacall(QObject *_o, QMetaObject::Call _c, int _id, void **_a)
{
    if (_c == QMetaObject::InvokeMetaMethod) {
        Q_ASSERT(staticMetaObject.cast(_o));
        CoverageListener *_t = static_cast<CoverageListener *>(_o);
        switch (_id) {
        case 0: _t->new_code((*reinterpret_cast< intptr_t(*)>(_a[1])),(*reinterpret_cast< QString(*)>(_a[2])),(*reinterpret_cast< QUrl(*)>(_a[3])),(*reinterpret_cast< int(*)>(_a[4]))); break;
        case 1: _t->statement_executed((*reinterpret_cast< intptr_t(*)>(_a[1])),(*reinterpret_cast< std::string(*)>(_a[2])),(*reinterpret_cast< int(*)>(_a[3]))); break;
        default: ;
        }
    }
}

const QMetaObjectExtraData artemis::CoverageListener::staticMetaObjectExtraData = {
    0,  qt_static_metacall 
};

const QMetaObject artemis::CoverageListener::staticMetaObject = {
    { &QObject::staticMetaObject, qt_meta_stringdata_artemis__CoverageListener,
      qt_meta_data_artemis__CoverageListener, &staticMetaObjectExtraData }
};

#ifdef Q_NO_DATA_RELOCATION
const QMetaObject &artemis::CoverageListener::getStaticMetaObject() { return staticMetaObject; }
#endif //Q_NO_DATA_RELOCATION

const QMetaObject *artemis::CoverageListener::metaObject() const
{
    return QObject::d_ptr->metaObject ? QObject::d_ptr->metaObject : &staticMetaObject;
}

void *artemis::CoverageListener::qt_metacast(const char *_clname)
{
    if (!_clname) return 0;
    if (!strcmp(_clname, qt_meta_stringdata_artemis__CoverageListener))
        return static_cast<void*>(const_cast< CoverageListener*>(this));
    return QObject::qt_metacast(_clname);
}

int artemis::CoverageListener::qt_metacall(QMetaObject::Call _c, int _id, void **_a)
{
    _id = QObject::qt_metacall(_c, _id, _a);
    if (_id < 0)
        return _id;
    if (_c == QMetaObject::InvokeMetaMethod) {
        if (_id < 2)
            qt_static_metacall(this, _c, _id, _a);
        _id -= 2;
    }
    return _id;
}
QT_END_MOC_NAMESPACE
