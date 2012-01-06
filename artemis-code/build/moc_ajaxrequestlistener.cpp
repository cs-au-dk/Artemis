/****************************************************************************
** Meta object code from reading C++ file 'ajaxrequestlistener.h'
**
** Created: Tue Jan 3 22:46:23 2012
**      by: The Qt Meta Object Compiler version 63 (Qt 4.8.0)
**
** WARNING! All changes made in this file will be lost!
*****************************************************************************/

#include "../src/ajax/ajaxrequestlistener.h"
#if !defined(Q_MOC_OUTPUT_REVISION)
#error "The header file 'ajaxrequestlistener.h' doesn't include <QObject>."
#elif Q_MOC_OUTPUT_REVISION != 63
#error "This file was generated using the moc from 4.8.0. It"
#error "cannot be used with the include files from this version of Qt."
#error "(The moc has changed too much.)"
#endif

QT_BEGIN_MOC_NAMESPACE
static const uint qt_meta_data_artemis__AjaxRequestListener[] = {

 // content:
       6,       // revision
       0,       // classname
       0,    0, // classinfo
       2,   14, // methods
       0,    0, // properties
       0,    0, // enums/sets
       0,    0, // constructors
       0,       // flags
       2,       // signalCount

 // signals: signature, parameters, type, tag, flags
      34,   30,   29,   29, 0x05,
      49,   30,   29,   29, 0x05,

       0        // eod
};

static const char qt_meta_stringdata_artemis__AjaxRequestListener[] = {
    "artemis::AjaxRequestListener\0\0url\0"
    "page_get(QUrl)\0page_post(QUrl)\0"
};

void artemis::AjaxRequestListener::qt_static_metacall(QObject *_o, QMetaObject::Call _c, int _id, void **_a)
{
    if (_c == QMetaObject::InvokeMetaMethod) {
        Q_ASSERT(staticMetaObject.cast(_o));
        AjaxRequestListener *_t = static_cast<AjaxRequestListener *>(_o);
        switch (_id) {
        case 0: _t->page_get((*reinterpret_cast< QUrl(*)>(_a[1]))); break;
        case 1: _t->page_post((*reinterpret_cast< QUrl(*)>(_a[1]))); break;
        default: ;
        }
    }
}

const QMetaObjectExtraData artemis::AjaxRequestListener::staticMetaObjectExtraData = {
    0,  qt_static_metacall 
};

const QMetaObject artemis::AjaxRequestListener::staticMetaObject = {
    { &QNetworkAccessManager::staticMetaObject, qt_meta_stringdata_artemis__AjaxRequestListener,
      qt_meta_data_artemis__AjaxRequestListener, &staticMetaObjectExtraData }
};

#ifdef Q_NO_DATA_RELOCATION
const QMetaObject &artemis::AjaxRequestListener::getStaticMetaObject() { return staticMetaObject; }
#endif //Q_NO_DATA_RELOCATION

const QMetaObject *artemis::AjaxRequestListener::metaObject() const
{
    return QObject::d_ptr->metaObject ? QObject::d_ptr->metaObject : &staticMetaObject;
}

void *artemis::AjaxRequestListener::qt_metacast(const char *_clname)
{
    if (!_clname) return 0;
    if (!strcmp(_clname, qt_meta_stringdata_artemis__AjaxRequestListener))
        return static_cast<void*>(const_cast< AjaxRequestListener*>(this));
    return QNetworkAccessManager::qt_metacast(_clname);
}

int artemis::AjaxRequestListener::qt_metacall(QMetaObject::Call _c, int _id, void **_a)
{
    _id = QNetworkAccessManager::qt_metacall(_c, _id, _a);
    if (_id < 0)
        return _id;
    if (_c == QMetaObject::InvokeMetaMethod) {
        if (_id < 2)
            qt_static_metacall(this, _c, _id, _a);
        _id -= 2;
    }
    return _id;
}

// SIGNAL 0
void artemis::AjaxRequestListener::page_get(QUrl _t1)
{
    void *_a[] = { 0, const_cast<void*>(reinterpret_cast<const void*>(&_t1)) };
    QMetaObject::activate(this, &staticMetaObject, 0, _a);
}

// SIGNAL 1
void artemis::AjaxRequestListener::page_post(QUrl _t1)
{
    void *_a[] = { 0, const_cast<void*>(reinterpret_cast<const void*>(&_t1)) };
    QMetaObject::activate(this, &staticMetaObject, 1, _a);
}
QT_END_MOC_NAMESPACE
