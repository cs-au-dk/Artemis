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

#ifndef EXPRESSIONVALUEPRINTER_H
#define EXPRESSIONVALUEPRINTER_H

#include <string>

#include "JavaScriptCore/symbolic/expr.h"
#include "JavaScriptCore/symbolic/expression/visitor.h"
#include "expressionprinter.h"

#ifdef ARTEMIS

namespace artemis
{

/**
 *  Behaves the same as ExpressionPrinter, except we print values whenever constants appear.
 *  TODO: Also print variable names whenever a symbolic input appears.
 */
class ExpressionValuePrinter : public ExpressionPrinter
{

public:

    void visit(Symbolic::ConstantInteger* constantinteger);
    void visit(Symbolic::ConstantString* constantstring);
    void visit(Symbolic::ConstantBoolean* constantboolean);

    void visit(Symbolic::SymbolicString* symbolicstring);

};

}

#endif
#endif // EXPRESSIONVALUEPRINTER_H
