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

#ifndef TRACEVISITOR_H
#define TRACEVISITOR_H

#include <QSharedPointer>


namespace artemis
{


// Need to forward declare the concrete nodes so we can reference them in the visitor.
class TraceNode;
class TraceBranch;
class TraceUnexplored;
class TraceAnnotation;
class TraceAlert;
class TraceDomModification;
class TracePageLoad;
class TraceEnd;
class TraceEndSuccess;
class TraceEndFailure;
class TraceEndUnknown;


/*
 *  The visitor interface.
 *  Implementations of this interface must implement visit() at least for TraceBranch but can also choose to
 *  implement special cases for specific node types as desired.
 */
class TraceVisitor
{
public:
    // Must be provided by a concrete visitor as a catch-all.
    virtual void visit(TraceNode* node) = 0;

    // Supply a default implementation for each node type which relays the call to the node type's parent type.
    // These can be overrriden as required by a concrete visitor.
    virtual void visit(TraceBranch* node);
    virtual void visit(TraceUnexplored* node);
    virtual void visit(TraceAnnotation* node);
    virtual void visit(TraceAlert* node);
    virtual void visit(TraceDomModification* node);
    virtual void visit(TracePageLoad* node);
    virtual void visit(TraceEnd* node);
    virtual void visit(TraceEndSuccess* node);
    virtual void visit(TraceEndFailure* node);
    virtual void visit(TraceEndUnknown* node);

    virtual ~TraceVisitor(){}
};

typedef QSharedPointer<TraceVisitor> TraceVisitorPtr;


} // namespace artemis

#endif // TRACEVISITOR_H
