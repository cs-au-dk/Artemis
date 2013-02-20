
#include <assert.h>
#include <util/randomutil.h>

#include <QSet>
#include <QList>

#include "runtime/events/forms/formfieldtypes.h"
#include "runtime/events/forms/forminput.h"

#include "dynamicforminputgenerator.h"

namespace artemis
{

DynamicFormInputGenerator::DynamicFormInputGenerator() : FormInputGenerator()
{

}

QSharedPointer<FormInput> DynamicFormInputGenerator::generateFormFields(QObject* parent, QSet<QSharedPointer<const FormField> > fields) const
{
    QSet<QPair<QSharedPointer<const FormField>, const FormFieldValue*> > inputs;

    foreach(QSharedPointer<const FormField> field, fields) {

        switch (field->getType()) {
        case TEXT:
            inputs.insert(QPair<QSharedPointer<const FormField>, const FormFieldValue*>(field, new FormFieldValue(parent, generateRandomString(10))));
            break;
        case BOOLEAN:
            inputs.insert(QPair<QSharedPointer<const FormField>, const FormFieldValue*>(field, new FormFieldValue(parent, randomBool())));
            break;
        case FIXED_INPUT:
            inputs.insert(QPair<QSharedPointer<const FormField>, const FormFieldValue*>(field, new FormFieldValue(parent, pickRand(field->getInputOptions()))));
            break;
        default:
            inputs.insert(QPair<QSharedPointer<const FormField>, const FormFieldValue*>(field, new FormFieldValue(parent)));
        }
    }

    return QSharedPointer<FormInput>(new FormInput(inputs));
}

}
