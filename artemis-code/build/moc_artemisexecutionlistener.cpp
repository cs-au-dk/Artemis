/****************************************************************************
** Meta object code from reading C++ file 'artemisexecutionlistener.h'
**
** Created: Tue Dec 20 14:39:05 2011
**      by: The Qt Meta Object Compiler version 63 (Qt 4.8.0)
**
** WARNING! All changes made in this file will be lost!
*****************************************************************************/

#include "../src/artemisexecutionlistener.h"
#if !defined(Q_MOC_OUTPUT_REVISION)
#error "The header file 'artemisexecutionlistener.h' doesn't include <QObject>."
#elif Q_MOC_OUTPUT_REVISION != 63
#error "This file was generated using the moc from 4.8.0. It"
#error "cannot be used with the include files from this version of Qt."
#error "(The moc has changed too much.)"
#endif

QT_BEGIN_MOC_NAMESPACE
static const uint qt_meta_data_artemis__ArtemisExecutionListener[] = {

 // content:
       6,       // revision
       0,       // classname
       0,    0, // classinfo
       4,   14, // methods
       0,    0, // properties
       0,    0, // enums/sets
       0,    0, // constructors
       0,       // flags
       0,       // signalCount

 // slots: signature, parameters, type, tag, flags
      37,   35,   34,   34, 0x0a,
      86,   35,   34,   34, 0x0a,
     152,  128,   34,   34, 0x0a,
     231,  197,   34,   34, 0x0a,

       0        // eod
};

static const char qt_meta_stringdata_artemis__ArtemisExecutionListener[] = {
    "artemis::ArtemisExecutionListener\0\0,\0"
    "newEventListenerRegistered(QWebElement*,QString)\0"
    "removeEventListener(QWebElement*,QString)\0"
    "id,source,url,startline\0"
    "newJavaScriptCode(intptr_t,QString,QUrl,int)\0"
    "sourceID,function_name,linenumber\0"
    "statementCovered(intptr_t,std::string,int)\0"
};

void artemis::ArtemisExecutionListener::qt_static_metacall(QObject *_o, QMetaObject::Call _c, int _id, void **_a)
{
    if (_c == QMetaObject::InvokeMetaMethod) {
        Q_ASSERT(staticMetaObject.cast(_o));
        ArtemisExecutionListener *_t = static_cast<ArtemisExecutionListener *>(_o);
        switch (_id) {
        case 0: _t->newEventListenerRegistered((*reinterpret_cast< QWebElement*(*)>(_a[1])),(*reinterpret_cast< QString(*)>(_a[2]))); break;
        case 1: _t->removeEventListener((*reinterpret_cast< QWebElement*(*)>(_a[1])),(*reinterpret_cast< QString(*)>(_a[2]))); break;
        case 2: _t->newJavaScriptCode((*reinterpret_cast< intptr_t(*)>(_a[1])),(*reinterpret_cast< QString(*)>(_a[2])),(*reinterpret_cast< QUrl(*)>(_a[3])),(*reinterpret_cast< int(*)>(_a[4]))); break;
        case 3: _t->statementCovered((*reinterpret_cast< intptr_t(*)>(_a[1])),(*reinterpret_cast< std::string(*)>(_a[2])),(*reinterpret_cast< int(*)>(_a[3]))); break;
        default: ;
        }
    }
}

const QMetaObjectExtraData artemis::ArtemisExecutionListener::staticMetaObjectExtraData = {
    0,  qt_static_metacall 
};

const QMetaObject artemis::ArtemisExecutionListener::staticMetaObject = {
    { &QObject::staticMetaObject, qt_meta_stringdata_artemis__ArtemisExecutionListener,
      qt_meta_data_artemis__ArtemisExecutionListener, &staticMetaObjectExtraData }
};

#ifdef Q_NO_DATA_RELOCATION
const QMetaObject &artemis::ArtemisExecutionListener::getStaticMetaObject() { return staticMetaObject; }
#endif //Q_NO_DATA_RELOCATION

const QMetaObject *artemis::ArtemisExecutionListener::metaObject() const
{
    return QObject::d_ptr->metaObject ? QObject::d_ptr->metaObject : &staticMetaObject;
}

void *artemis::ArtemisExecutionListener::qt_metacast(const char *_clname)
{
    if (!_clname) return 0;
    if (!strcmp(_clname, qt_meta_stringdata_artemis__ArtemisExecutionListener))
        return static_cast<void*>(const_cast< ArtemisExecutionListener*>(this));
    return QObject::qt_metacast(_clname);
}

int artemis::ArtemisExecutionListener::qt_metacall(QMetaObject::Call _c, int _id, void **_a)
{
    _id = QObject::qt_metacall(_c, _id, _a);
    if (_id < 0)
        return _id;
    if (_c == QMetaObject::InvokeMetaMethod) {
        if (_id < 4)
            qt_static_metacall(this, _c, _id, _a);
        _id -= 4;
    }
    return _id;
}
QT_END_MOC_NAMESPACE
