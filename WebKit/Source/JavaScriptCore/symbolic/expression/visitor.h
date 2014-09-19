/*
 * Copyright 2012 Aarhus University
 *
 * Licensed under the GNU General Public License, Version 3 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *          http://www.gnu.org/licenses/gpl-3.0.html
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

// Move this to another file?
enum Type {
	INT, BOOL, STRING, OBJECT, TYPEERROR
};

    class SymbolicInteger;
    class ConstantInteger;
    class IntegerBinaryOperation;
    class IntegerCoercion;
    class IntegerMaxMin;
    class ConstantObject;
    class ObjectBinaryOperation;
    class SymbolicString;
    class ConstantString;
    class StringBinaryOperation;
    class StringCoercion;
    class StringLength;
    class StringReplace;
    class StringIndexOf;
    class StringCharAt;
    class StringRegexReplace;
    class StringRegexSubmatch;
    class StringRegexSubmatchIndex;
    class StringRegexSubmatchArray;
    class StringRegexSubmatchArrayAt;
    class StringRegexSubmatchArrayMatch;
    class SymbolicBoolean;
    class ConstantBoolean;
    class BooleanCoercion;
    class BooleanBinaryOperation;

class Visitor
{

public:
    virtual void visit(SymbolicInteger* symbolicinteger, void* arg) = 0;
    virtual void visit(ConstantInteger* constantinteger, void* arg) = 0;
    virtual void visit(IntegerBinaryOperation* integerbinaryoperation, void* arg) = 0;
    virtual void visit(IntegerCoercion* integercoercion, void* arg) = 0;
    virtual void visit(IntegerMaxMin* integermaxmin, void* arg) = 0;
    virtual void visit(ConstantObject* constantobject, void* arg) = 0;
    virtual void visit(ObjectBinaryOperation* objectbinaryoperation, void* arg) = 0;
    virtual void visit(SymbolicString* symbolicstring, void* arg) = 0;
    virtual void visit(ConstantString* constantstring, void* arg) = 0;
    virtual void visit(StringBinaryOperation* stringbinaryoperation, void* arg) = 0;
    virtual void visit(StringCoercion* stringcoercion, void* arg) = 0;
    virtual void visit(StringLength* stringlength, void* arg) = 0;
    virtual void visit(StringReplace* stringreplace, void* arg) = 0;
    virtual void visit(StringIndexOf* stringindexof, void* arg) = 0;
    virtual void visit(StringCharAt* stringcharat, void* arg) = 0;
    virtual void visit(StringRegexReplace* stringregexreplace, void* arg) = 0;
    virtual void visit(StringRegexSubmatch* stringregexsubmatch, void* arg) = 0;
    virtual void visit(StringRegexSubmatchIndex* stringregexsubmatchindex, void* arg) = 0;
    virtual void visit(StringRegexSubmatchArray* stringregexsubmatcharray, void* arg) = 0;
    virtual void visit(StringRegexSubmatchArrayAt* stringregexsubmatcharrayat, void* arg) = 0;
    virtual void visit(StringRegexSubmatchArrayMatch* stringregexsubmatcharraymatch, void* arg) = 0;
    virtual void visit(SymbolicBoolean* symbolicboolean, void* arg) = 0;
    virtual void visit(ConstantBoolean* constantboolean, void* arg) = 0;
    virtual void visit(BooleanCoercion* booleancoercion, void* arg) = 0;
    virtual void visit(BooleanBinaryOperation* booleanbinaryoperation, void* arg) = 0;

};

}

#endif
#endif
