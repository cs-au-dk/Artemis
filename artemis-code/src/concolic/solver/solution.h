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

#ifndef SOLUTION_H
#define SOLUTION_H

#include <QSharedPointer>
#include <QHash>
#include <QString>

#include "JavaScriptCore/symbolic/expression/visitor.h"

namespace artemis
{

typedef struct {
    bool found;
    Symbolic::Type kind;

    union {
       bool boolean;
       int integer;
    } u;

    std::string string; // we can't add the string inside the union :(

} Symbolvalue;


class Solution
{

public:
    Solution(bool success, bool unsat);

    bool isSolved() const;
    bool isUnsat() const;
    void insertSymbol(QString symbol, Symbolvalue value);
    Symbolvalue findSymbol(QString symbol);

    void toStatistics();

private:
    bool mSuccess;
    bool mUnsat;
    QHash<QString, Symbolvalue> mSymbols;
};

typedef QSharedPointer<Solution> SolutionPtr;

}

#endif // SOLUTION_H
