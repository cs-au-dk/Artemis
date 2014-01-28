
//#include <QSharedPointer>
//#include <QString>
//#include <QSet>
//#include <QList>

#include "include/gtest/gtest.h"

//#include "strategies/inputgenerator/form/constantstringforminputgenerator.h"
//#include "runtime/input/forms/formfielddescriptor.h"

namespace artemis
{
/*
 *
 * Disable these tests, needs review
TEST(ConstantStringInputGeneratorTest, NoConstantsObserved) {

    ConstantStringFormInputGeneratorPtr inputGenerator = \
            ConstantStringFormInputGeneratorPtr(new ConstantStringFormInputGenerator(QList<QString>()));

    QSharedPointer<const ExecutionResult> result = QSharedPointer<ExecutionResult>(new ExecutionResult());

    QSet<FormFieldDescriptorConstPtr> fields;
    fields.insert(FormFieldDescriptorConstPtr(new FormFieldDescriptor(TEXT, DOMElementDescriptorConstPtr())));

    FormInputCollectionPtr formInput = inputGenerator->generateFormFields(fields, result);

    ASSERT_EQ(1, formInput->getInputs().size());
}

TEST(ConstantStringInputGeneratorTest, SingleConstantObserved) {

    ConstantStringFormInputGeneratorPtr inputGenerator = \
            ConstantStringFormInputGeneratorPtr(new ConstantStringFormInputGenerator(QList<QString>()));

    ExecutionResultPtr result = ExecutionResultPtr(new ExecutionResult());
    result->addJavascriptConstantObservedForLastEvent("constant-string");

    QSet<FormFieldDescriptorConstPtr> fields;
    fields.insert(FormFieldDescriptorConstPtr(new FormFieldDescriptor(TEXT, DOMElementDescriptorConstPtr())));

    FormInputCollectionPtr formInput = inputGenerator->generateFormFields(fields, result);

    ASSERT_EQ(1, formInput->getInputs().size());

    QString value = formInput->getInputs().at(0).second;
    ASSERT_EQ(value.toStdString(), "constant-string");
}*/

}
