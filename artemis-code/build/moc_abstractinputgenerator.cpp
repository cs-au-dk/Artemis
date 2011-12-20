/****************************************************************************
** Meta object code from reading C++ file 'abstractinputgenerator.h'
**
** Created: Tue Dec 20 14:39:06 2011
**      by: The Qt Meta Object Compiler version 63 (Qt 4.8.0)
**
** WARNING! All changes made in this file will be lost!
*****************************************************************************/

#include "../src/inputgenerator/abstractinputgenerator.h"
#if !defined(Q_MOC_OUTPUT_REVISION)
#error "The header file 'abstractinputgenerator.h' doesn't include <QObject>."
#elif Q_MOC_OUTPUT_REVISION != 63
#error "This file was generated using the moc from 4.8.0. It"
#error "cannot be used with the include files from this version of Qt."
#error "(The moc has changed too much.)"
#endif

QT_BEGIN_MOC_NAMESPACE
static const uint qt_meta_data_artemis__AbstractInputGenerator[] = {

 // content:
       6,       // revision
       0,       // classname
       0,    0, // classinfo
       2,   14, // methods
       0,    0, // properties
       0,    0, // enums/sets
       0,    0, // constructors
       0,       // flags
       1,       // signalCount

 // signals: signature, parameters, type, tag, flags
      33,   32,   32,   32, 0x05,

 // slots: signature, parameters, type, tag, flags
      60,   51,   32,   32, 0x0a,

       0        // eod
};

static const char qt_meta_stringdata_artemis__AbstractInputGenerator[] = {
    "artemis::AbstractInputGenerator\0\0"
    "sig_testingDone()\0conf,res\0"
    "sl_executorExecutedSequence(ExecutableConfiguration,ExecutionResult)\0"
};

void artemis::AbstractInputGenerator::qt_static_metacall(QObject *_o, QMetaObject::Call _c, int _id, void **_a)
{
    if (_c == QMetaObject::InvokeMetaMethod) {
        Q_ASSERT(staticMetaObject.cast(_o));
        AbstractInputGenerator *_t = static_cast<AbstractInputGenerator *>(_o);
        switch (_id) {
        case 0: _t->sig_testingDone(); break;
        case 1: _t->sl_executorExecutedSequence((*reinterpret_cast< ExecutableConfiguration(*)>(_a[1])),(*reinterpret_cast< ExecutionResult(*)>(_a[2]))); break;
        default: ;
        }
    }
}

const QMetaObjectExtraData artemis::AbstractInputGenerator::staticMetaObjectExtraData = {
    0,  qt_static_metacall 
};

const QMetaObject artemis::AbstractInputGenerator::staticMetaObject = {
    { &QObject::staticMetaObject, qt_meta_stringdata_artemis__AbstractInputGenerator,
      qt_meta_data_artemis__AbstractInputGenerator, &staticMetaObjectExtraData }
};

#ifdef Q_NO_DATA_RELOCATION
const QMetaObject &artemis::AbstractInputGenerator::getStaticMetaObject() { return staticMetaObject; }
#endif //Q_NO_DATA_RELOCATION

const QMetaObject *artemis::AbstractInputGenerator::metaObject() const
{
    return QObject::d_ptr->metaObject ? QObject::d_ptr->metaObject : &staticMetaObject;
}

void *artemis::AbstractInputGenerator::qt_metacast(const char *_clname)
{
    if (!_clname) return 0;
    if (!strcmp(_clname, qt_meta_stringdata_artemis__AbstractInputGenerator))
        return static_cast<void*>(const_cast< AbstractInputGenerator*>(this));
    return QObject::qt_metacast(_clname);
}

int artemis::AbstractInputGenerator::qt_metacall(QMetaObject::Call _c, int _id, void **_a)
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

// SIGNAL 0
void artemis::AbstractInputGenerator::sig_testingDone()
{
    QMetaObject::activate(this, &staticMetaObject, 0, 0);
}
QT_END_MOC_NAMESPACE
