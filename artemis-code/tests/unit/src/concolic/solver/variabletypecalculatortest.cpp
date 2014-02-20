#include "include/gtest/gtest.h"

#include <QMap>
#include <QString>
#include <QSet>

#include "concolic/pathcondition.h"
#include "JavaScriptCore/symbolic/expr.h"
#include "concolic/solver/variabletypecalculator.h"

namespace artemis
{

TEST(VariableTypeCalculatorTest, SAMPLE_EXPR) {
    // The expression given as an example in variabletypecalculator.cpp.
    // IntegerBinaryOperation(IntegerCoercion(v1), INT_EQ, IntegerCoercion(StringBinaryOperation(v1, CONCAT, v2)))

    // Set up the symbolic expression
    Symbolic::SymbolicString input1 = Symbolic::SymbolicString(Symbolic::SymbolicSource(Symbolic::INPUT, Symbolic::ELEMENT_ID, "Var1"));
    Symbolic::SymbolicString input2 = Symbolic::SymbolicString(Symbolic::SymbolicSource(Symbolic::INPUT, Symbolic::ELEMENT_ID, "Var2"));
    Symbolic::IntegerCoercion integercoercion1 = Symbolic::IntegerCoercion(&input1);
    Symbolic::StringBinaryOperation stringbinaryoperation = Symbolic::StringBinaryOperation(&input1, Symbolic::CONCAT, &input2);
    Symbolic::IntegerCoercion integercoercion2 = Symbolic::IntegerCoercion(&stringbinaryoperation);
    Symbolic::IntegerBinaryOperation integerbinaryoperation = Symbolic::IntegerBinaryOperation(&integercoercion1, Symbolic::INT_EQ, &integercoercion2);

    // Set up the path condition
    PathConditionPtr testpc = PathConditionPtr(new PathCondition());
    testpc->addCondition(&integerbinaryoperation, true);

    // Expected results
    QSet<QString> stringVars, intVars, boolVars;
    stringVars.insert("Var1");
    stringVars.insert("Var2");
    intVars.insert("Var1");

    QMap<QString, Symbolic::Type> expected;
    expected.insert("Var1", Symbolic::STRING);
    expected.insert("Var2", Symbolic::STRING);

    // Run the test
    VariableTypeCalculator calculator;
    QMap<QString, Symbolic::Type> result = calculator.calculateTypes(testpc);

    EXPECT_EQ(stringVars, calculator.getStringVars());
    EXPECT_EQ(intVars, calculator.getIntVars());
    EXPECT_EQ(boolVars, calculator.getBoolVars());
    ASSERT_EQ(expected, result);
}


TEST(VariableTypeCalculatorTest, INT_COERCION) {
    // IntegerBinaryOperation(IntegerCoercion(Var1), INT_EQ, IntegerCoercion(Var2))

    // Set up the expression and PC
    Symbolic::SymbolicString input1 = Symbolic::SymbolicString(Symbolic::SymbolicSource(Symbolic::INPUT, Symbolic::ELEMENT_ID, "Var1"));
    Symbolic::SymbolicString input2 = Symbolic::SymbolicString(Symbolic::SymbolicSource(Symbolic::INPUT, Symbolic::ELEMENT_ID, "Var2"));
    Symbolic::IntegerCoercion integercoercion1 = Symbolic::IntegerCoercion(&input1);
    Symbolic::IntegerCoercion integercoercion2 = Symbolic::IntegerCoercion(&input2);
    Symbolic::IntegerBinaryOperation integerbinaryoperation = Symbolic::IntegerBinaryOperation(&integercoercion1, Symbolic::INT_EQ, &integercoercion2);
    PathConditionPtr testpc = PathConditionPtr(new PathCondition());
    testpc->addCondition(&integerbinaryoperation, true);

    // Expected results
    QSet<QString> stringVars, intVars, boolVars;
    intVars.insert("Var1");
    intVars.insert("Var2");

    QMap<QString, Symbolic::Type> expected;
    expected.insert("Var1", Symbolic::INT);
    expected.insert("Var2", Symbolic::INT);

    // Run the test
    VariableTypeCalculator calculator;
    QMap<QString, Symbolic::Type> result = calculator.calculateTypes(testpc);

    EXPECT_EQ(stringVars, calculator.getStringVars());
    EXPECT_EQ(intVars, calculator.getIntVars());
    EXPECT_EQ(boolVars, calculator.getBoolVars());
    ASSERT_EQ(expected, result);
}

TEST(VariableTypeCalculatorTest, BOOL_COERCION) {
    // BooleanCoercion(Var1)

    // Set up the expression and PC
    Symbolic::SymbolicString input1 = Symbolic::SymbolicString(Symbolic::SymbolicSource(Symbolic::INPUT, Symbolic::ELEMENT_ID, "Var1"));
    Symbolic::BooleanCoercion booleancoercion1 = Symbolic::BooleanCoercion(&input1);
    PathConditionPtr testpc = PathConditionPtr(new PathCondition());
    testpc->addCondition(&booleancoercion1, true);

    // Expected results
    QSet<QString> stringVars, intVars, boolVars;
    boolVars.insert("Var1");

    QMap<QString, Symbolic::Type> expected;
    expected.insert("Var1", Symbolic::BOOL);

    // Run the test
    VariableTypeCalculator calculator;
    QMap<QString, Symbolic::Type> result = calculator.calculateTypes(testpc);

    EXPECT_EQ(stringVars, calculator.getStringVars());
    EXPECT_EQ(intVars, calculator.getIntVars());
    EXPECT_EQ(boolVars, calculator.getBoolVars());
    ASSERT_EQ(expected, result);
}


TEST(VariableTypeCalculatorTest, STRING_VARS) {
    // StringBinaryOperation(v1, CONCAT, v2)

    // Set up the symbolic expression and PC.
    Symbolic::SymbolicString input1 = Symbolic::SymbolicString(Symbolic::SymbolicSource(Symbolic::INPUT, Symbolic::ELEMENT_ID, "Var1"));
    Symbolic::SymbolicString input2 = Symbolic::SymbolicString(Symbolic::SymbolicSource(Symbolic::INPUT, Symbolic::ELEMENT_ID, "Var2"));
    Symbolic::StringBinaryOperation stringbinaryoperation = Symbolic::StringBinaryOperation(&input1, Symbolic::CONCAT, &input2);
    PathConditionPtr testpc = PathConditionPtr(new PathCondition());
    testpc->addCondition(&stringbinaryoperation, true);

    // Expected results
    QSet<QString> stringVars, intVars, boolVars;
    stringVars.insert("Var1");
    stringVars.insert("Var2");

    QMap<QString, Symbolic::Type> expected;
    expected.insert("Var1", Symbolic::STRING);
    expected.insert("Var2", Symbolic::STRING);

    // Run the test
    VariableTypeCalculator calculator;
    QMap<QString, Symbolic::Type> result = calculator.calculateTypes(testpc);

    EXPECT_EQ(stringVars, calculator.getStringVars());
    EXPECT_EQ(intVars, calculator.getIntVars());
    EXPECT_EQ(boolVars, calculator.getBoolVars());
    ASSERT_EQ(expected, result);
}


TEST(VariableTypeCalculatorTest, MULTI_EXPR_PC) {
    // Set up the expressions and PC
    Symbolic::SymbolicBoolean input1 = Symbolic::SymbolicBoolean(Symbolic::SymbolicSource(Symbolic::INPUT, Symbolic::ELEMENT_ID, "Var1"));
    Symbolic::SymbolicBoolean input2 = Symbolic::SymbolicBoolean(Symbolic::SymbolicSource(Symbolic::INPUT, Symbolic::ELEMENT_ID, "Var2"));
    PathConditionPtr testpc = PathConditionPtr(new PathCondition());
    testpc->addCondition(&input1, true);
    testpc->addCondition(&input2, true);

    // Expected results
    QSet<QString> stringVars, intVars, boolVars;
    boolVars.insert("Var1");
    boolVars.insert("Var2");

    QMap<QString, Symbolic::Type> expected;
    expected.insert("Var1", Symbolic::BOOL);
    expected.insert("Var2", Symbolic::BOOL);

    // Run the test
    VariableTypeCalculator calculator;
    QMap<QString, Symbolic::Type> result = calculator.calculateTypes(testpc);

    EXPECT_EQ(stringVars, calculator.getStringVars());
    EXPECT_EQ(intVars, calculator.getIntVars());
    EXPECT_EQ(boolVars, calculator.getBoolVars());
    ASSERT_EQ(expected, result);
}



// TODO: Test each feature of the expressions separately (if feasible?)



} //namespace artemis
