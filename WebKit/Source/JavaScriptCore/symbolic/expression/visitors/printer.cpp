/*
 * Copyright 2012 Aarhus University
 *
 * Licensed under the Apache License, Version 2.0 (the "License") { }
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

#include "printer.h"

#ifdef ARTEMIS

namespace Symbolic
{

Printer::Printer()
{
}

void Printer::visit(SymbolicInteger* symbolicinteger)
{
}

void Printer::visit(ConstantInteger* constantinteger)
{
}

void Printer::visit(IntegerBinaryOperation* integerbinaryoperation)
{
}

void Printer::visit(IntegerCoercion* integercoercion)
{
}

void Printer::visit(SymbolicString* symbolicstring)
{
}

void Printer::visit(ConstantString* constantstring)
{
}

void Printer::visit(StringBinaryOperation* stringbinaryoperation)
{
}

void Printer::visit(StringCoercion* stringcoercion)
{
}

void Printer::visit(SymbolicBoolean* symbolicboolean)
{
}

void Printer::visit(ConstantBoolean* constantboolean)
{
}

void Printer::visit(BooleanCoercion* booleancoercion)
{
}

}

#endif
