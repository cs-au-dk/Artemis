
#include <QSharedPointer>

#include "include/gtest/gtest.h"

#include "strategies/inputgenerator/form/constantstringforminputgenerator.h"

namespace artemis
{

TEST(ConstantStringInputGeneratorTest, NoConstantsObserved) {

    QSharedPointer<ConstantStringFormInputGenerator> inputGenerator = QSharedPointer<ConstantStringFormInputGenerator>(new ConstantStringFormInputGenerator());
    QSharedPointer<const ExecutionResult> result = QSharedPointer<ExecutionResult>(new ExecutionResult());

    QSet<QSharedPointer<const FormField> > fields;
    fields.insert(QSharedPointer<FormField>(new FormField(TEXT, NULL)));

    QSharedPointer<FormInput> formInput = inputGenerator->generateFormFields(NULL, fields, result);

    ASSERT_EQ(1, formInput->getInputs().size());
}

TEST(ConstantStringInputGeneratorTest, SingleConstantObserved) {

    QSharedPointer<ConstantStringFormInputGenerator> inputGenerator = QSharedPointer<ConstantStringFormInputGenerator>(new ConstantStringFormInputGenerator());

    QSharedPointer<ExecutionResult> result = QSharedPointer<ExecutionResult>(new ExecutionResult());
    result->addJavascriptConstantObservedForLastEvent("constant-string");

    QSet<QSharedPointer<const FormField> > fields;
    fields.insert(QSharedPointer<FormField>(new FormField(TEXT, NULL)));

    QSharedPointer<FormInput> formInput = inputGenerator->generateFormFields(NULL, fields, result);

    ASSERT_EQ(1, formInput->getInputs().size());

    const FormFieldValue* value = formInput->getInputs().toList().at(0).second;
    ASSERT_EQ(value->getStr().toStdString(), "constant-string");
}

}
