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

#include "concreteinput.h"

#ifndef TRACE_H
#define TRACE_H

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



// Need to forward declare the concrete nodes so we can reference them in the visitor.
class TraceNode; //...?
class TraceBranch;
class TraceUnexplored;
class TraceAlert;
class TraceDomModification;
class TracePageLoad;
class TraceEndSuccess;
class TraceEndFailure;
class TraceEndUnknown;


// The visitor interface.
/*
class TraceVisitor
{
public:
    virtual void visit(QSharedPointer<TraceBranch> node) = 0;
    virtual void visit(QSharedPointer<TraceUnexplored> node) = 0;
    virtual void visit(QSharedPointer<TraceAlert> node) = 0;
    virtual void visit(QSharedPointer<TraceDomModification> node) = 0;
    virtual void visit(QSharedPointer<TracePageLoad> node) = 0;
    virtual void visit(QSharedPointer<TraceEndSuccess> node) = 0;
    virtual void visit(QSharedPointer<TraceEndFailure> node) = 0;
    virtual void visit(QSharedPointer<TraceEndUnknown> node) = 0;
    virtual ~TraceVisitor(){}
};
*/
class TraceVisitor
{
public:
    virtual void visit(QSharedPointer<TraceNode>) = 0;
    virtual ~TraceVisitor(){}
};

typedef QSharedPointer<TraceVisitor> TraceVisitorPtr;



// The node types.
class TraceNode
{
    // Abstract
public:
    virtual void accept(TraceVisitorPtr visitor) = 0;
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
    void accept(TraceVisitorPtr visitor){visitor->visit(QSharedPointer<TraceBranch>(this));}
    ~TraceBranch(){}
};


class TraceUnexplored : public TraceNode
{
    // This is just a placeholder for unexplored parts of the tree.
public:
    void accept(TraceVisitorPtr visitor){visitor->visit(QSharedPointer<TraceUnexplored>(this));}
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
    void accept(TraceVisitorPtr visitor){visitor->visit(QSharedPointer<TraceAlert>(this));}
    ~TraceAlert(){}
};


class TraceDomModification : public TraceAnnotation
{
public:
    int amountModified; // TODO: type? how is this measured?
    void accept(TraceVisitorPtr visitor){visitor->visit(QSharedPointer<TraceDomModification>(this));}
    ~TraceDomModification(){}
};


class TracePageLoad : public TraceAnnotation
{
public:
    QString page; // TODO: should we keep both the old and new pages?
    void accept(TraceVisitorPtr visitor){visitor->visit(QSharedPointer<TracePageLoad>(this));}
    ~TracePageLoad(){}
};


class TraceEnd : public TraceNode
{
    // Abstract
};


class TraceEndSuccess : public TraceEnd
{
    // Empty placeholder.
public:
    void accept(TraceVisitorPtr visitor){visitor->visit(QSharedPointer<TraceEndSuccess>(this));}
    ~TraceEndSuccess(){}
};


class TraceEndFailure : public TraceEnd
{
    // Empty placeholder.
public:
    void accept(TraceVisitorPtr visitor){visitor->visit(QSharedPointer<TraceEndFailure>(this));}
    ~TraceEndFailure(){}
};


class TraceEndUnknown : public TraceEnd
{
    // Empty placeholder.
public:
    void accept(TraceVisitorPtr visitor){visitor->visit(QSharedPointer<TraceEndUnknown>(this));}
    ~TraceEndUnknown(){}
};






}


#endif // TRACE_H
