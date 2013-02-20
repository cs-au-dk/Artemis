
#include <iostream>
#include <assert.h>
#include <util/randomutil.h>

#include <QSet>
#include <QList>

#include "runtime/events/forms/formfieldtypes.h"
#include "runtime/events/forms/forminput.h"

#include "constantstringforminputgenerator.h"

namespace artemis
{

ConstantStringFormInputGenerator::ConstantStringFormInputGenerator() : FormInputGenerator()
{

}

/**
 * This strategy relies on constant strings extracted from the latest JavaScript run for text input fields.
 *
 * All other field types are handled using the random strategy.
 */
QSharedPointer<FormInput> ConstantStringFormInputGenerator::generateFormFields(QObject* parent,
                                                                        QSet<QSharedPointer<const FormField> > fields,
                                                                        QSharedPointer<const ExecutionResult> executionResult) const
{
    QSet<QPair<QSharedPointer<const FormField>, const FormFieldValue*> > inputs;

    foreach(QSharedPointer<const FormField> field, fields) {

        switch (field->getType()) {
        case TEXT:
            if (executionResult->getJavascriptConstantsObservedForLastEvent().size() == 0) {
                inputs.insert(QPair<QSharedPointer<const FormField>, const FormFieldValue*>(field, new FormFieldValue(parent, generateRandomString(10))));
            } else {
                inputs.insert(QPair<QSharedPointer<const FormField>, const FormFieldValue*>(field,
                    new FormFieldValue(parent, pickRand(executionResult->getJavascriptConstantsObservedForLastEvent()))));
            }
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
