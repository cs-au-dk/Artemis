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

#ifndef TRACE_H
#define TRACE_H

#include <QSharedPointer>
#include <QString>
#include <QList>

#include "JavaScriptCore/symbolic/expr.h"

#include "concolic/executiontree/tracevisitor.h"

namespace artemis
{

class TraceNode
{
    // Abstract
public:
    virtual void accept(TraceVisitor* visitor) = 0;
    virtual ~TraceNode(){}
};

typedef QSharedPointer<TraceNode> TraceNodePtr;

class TraceAnnotation : public TraceNode
{
    // Abstract
public:
    TraceNodePtr next;
};


class TraceAlert : public TraceAnnotation
{
public:
    QString message;
    void accept(TraceVisitor* visitor){visitor->visit(this);}
    ~TraceAlert(){}
};


class TraceDomModification : public TraceAnnotation
{
public:
    int amountModified; // TODO: type? how is this measured?
    void accept(TraceVisitor* visitor){visitor->visit(this);}
    ~TraceDomModification(){}
};


class TracePageLoad : public TraceAnnotation
{
public:
    QString page; // TODO: should we keep both the old and new pages?
    void accept(TraceVisitor* visitor){visitor->visit(this);}
    ~TracePageLoad(){}
};


class TraceFunctionCall : public TraceAnnotation
{
public:
    QString name;
    void accept(TraceVisitor* visitor){visitor->visit(this);}
    ~TraceFunctionCall(){}
};


class TraceEnd : public TraceNode
{
    // Abstract
};


class TraceEndSuccess : public TraceEnd
{
    // Empty placeholder.
public:
    void accept(TraceVisitor* visitor){visitor->visit(this);}
    ~TraceEndSuccess(){}
};


class TraceEndFailure : public TraceEnd
{
    // Empty placeholder.
public:
    void accept(TraceVisitor* visitor){visitor->visit(this);}
    ~TraceEndFailure(){}
};


class TraceEndUnknown : public TraceEnd
{
    // Empty placeholder.
public:
    void accept(TraceVisitor* visitor){visitor->visit(this);}
    ~TraceEndUnknown(){}
};






}


#endif // TRACE_H
