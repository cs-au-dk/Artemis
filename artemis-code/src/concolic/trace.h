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


#include <QSharedPointer>
#include <QString>
#include <QList>


#ifndef TRACE_H
#define TRACE_H

#include "concreteinput.h"
#include "tracevisitor.h"


namespace artemis
{





/*
 *  The various types of trace node which are used.
 *  These are used both for recording a single trace and the nodes in the path tree.
 *
 *  A single trace is jsut a sequence of TraceNodes.
 *  TraceBranch nodes come from the WebKit instrumentation.
 *  TraceAnnotation nodes come from the "interesting event detectors".
 *      They are used by the classifier and must be ignored by the search algorithm.
 *  TraceEnd nodes are added by the classifier and used by the search algorithm.
 *  TraceUnexplored nodes are only used in the path tree and
 *
 *  We also have a visitor interface to allow these traces (and trees) to be explored.
 */

/*
 *  Note on pointers:
 *  We must use standard pointers instead of smart pointers here, because in the visitor pattern a node must pass
 *  out a reference to itself. If this reference is wrapped in a shared pointer then as soon as that pointer goes
 *  out of scope the node will be deleted.
 *  So the visitor parts use standard pointers and have the following restrictions:
 *      * A visitor must never store a node pointer.
 *      * A visitor cannot guarantee that a pointer is still valid if modifications are made higher up the tree
 *          which may have caused it to become unreferenced by any smart pointer.
 */


class TraceNode
{
    // Abstract
public:
    virtual void accept(TraceVisitor* visitor) = 0;
    virtual ~TraceNode(){}
};

typedef QSharedPointer<TraceNode> TraceNodePtr;


class TraceBranch : public TraceNode
{
public:
    TraceNodePtr branchTrue;
    TraceNodePtr branchFalse;
    QString condition; // TODO: type?
    QString symCondition; // TODO; type? is this needed?
    void accept(TraceVisitor* visitor){visitor->visit(this);}
    ~TraceBranch(){}
};


class TraceUnexplored : public TraceNode
{
    // This is just a placeholder for unexplored parts of the tree.
public:
    void accept(TraceVisitor* visitor){visitor->visit(this);}
    ~TraceUnexplored(){}
};


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
