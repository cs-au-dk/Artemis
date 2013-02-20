#ifndef DYNAMICFORMINPUTGENERATOR_H
#define DYNAMICFORMINPUTGENERATOR_H

#include "forminputgenerator.h"

namespace artemis
{

class DynamicFormInputGenerator : public FormInputGenerator
{
public:

    DynamicFormInputGenerator();

    QSharedPointer<FormInput> generateFormFields(QObject* parent, QSet<QSharedPointer<const FormField> > fi) const;

};

}

#endif // DYNAMICFORMINPUTGENERATOR_H
