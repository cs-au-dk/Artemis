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

#ifndef CVC4_H
#define CVC4_H

#include <fstream>
#include <map>

#include <QSharedPointer>

#include "JavaScriptCore/symbolic/expr.h"
#include "JavaScriptCore/symbolic/expression/visitor.h"

#include "smt.h"
#include "abstract.h"

namespace artemis
{

class CVC4ConstraintWriter : public SMTConstraintWriter
{
public:

    CVC4ConstraintWriter();

protected:
    virtual void visit(Symbolic::StringLength* stringlength, void* args);

    virtual void visit(Symbolic::SymbolicString* symbolicstring, void* args);
    virtual void visit(Symbolic::ConstantString* constantstring, void* args);
    virtual void visit(Symbolic::StringBinaryOperation* stringbinaryoperation, void* args);
    virtual void visit(Symbolic::StringCoercion* stringcoercion, void* args);
    virtual void visit(Symbolic::StringRegexReplace* stringregexreplace, void* args);
    virtual void visit(Symbolic::StringReplace* stringreplace, void* args);

    virtual void preVisitPathConditionsHook();
    virtual void postVisitPathConditionsHook();
};

typedef QSharedPointer<CVC4ConstraintWriter> CVC4ConstraintWriterPtr;

}

#endif // Z3STR_H
