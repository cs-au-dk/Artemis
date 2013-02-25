#ifndef DYNAMICFORMINPUTGENERATOR_H
#define DYNAMICFORMINPUTGENERATOR_H

#include "forminputgenerator.h"

namespace artemis
{

class ConstantStringFormInputGenerator : public FormInputGenerator
{
public:

    ConstantStringFormInputGenerator();

    QSharedPointer<FormInput> generateFormFields(QObject* parent,
                                                 QSet<QSharedPointer<const FormField> > fi,
                                                 QSharedPointer<const ExecutionResult> executionResult) const;

};

}

#endif // DYNAMICFORMINPUTGENERATOR_H
