/*
 * Copyright 2012 Aarhus University
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

 // AUTO GENERATED - DO NOT MODIFY

#ifdef ARTEMIS


#ifndef SYMBOLIC_VISITOR_H
#define SYMBOLIC_VISITOR_H

namespace Symbolic
{

    class SymbolicInteger;
    class ConstantInteger;
    class IntegerBinaryOperation;
    class BooleanBinaryOperation;
    class IntegerCoercion;
    class SymbolicString;
    class ConstantString;
    class StringBinaryOperation;
    class StringCoercion;
    class SymbolicBoolean;
    class ConstantBoolean;
    class BooleanCoercion;
    class BooleanBinaryOperation;

class Visitor
{

public:
    virtual void visit(SymbolicInteger* symbolicinteger) = 0;
    virtual void visit(ConstantInteger* constantinteger) = 0;
    virtual void visit(IntegerBinaryOperation* integerbinaryoperation) = 0;
    virtual void visit(BooleanBinaryOperation* booleanbinaryoperation) = 0;
    virtual void visit(IntegerCoercion* integercoercion) = 0;
    virtual void visit(SymbolicString* symbolicstring) = 0;
    virtual void visit(ConstantString* constantstring) = 0;
    virtual void visit(StringBinaryOperation* stringbinaryoperation) = 0;
    virtual void visit(StringCoercion* stringcoercion) = 0;
    virtual void visit(SymbolicBoolean* symbolicboolean) = 0;
    virtual void visit(ConstantBoolean* constantboolean) = 0;
    virtual void visit(BooleanCoercion* booleancoercion) = 0;
    virtual void visit(BooleanBinaryOperation* booleanbinaryoperation) = 0;

};

}

#endif
#endif
