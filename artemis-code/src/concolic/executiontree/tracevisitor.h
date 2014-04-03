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

#ifndef TRACEVISITOR_H
#define TRACEVISITOR_H

#include <QSharedPointer>


namespace artemis
{


// Need to forward declare the concrete nodes so we can reference them in the visitor.
class TraceNode;
class TraceBranch;
class TraceConcreteBranch;
class TraceSymbolicBranch;
class TraceUnexplored;
class TraceUnexploredUnsat;
class TraceUnexploredUnsolvable;
class TraceUnexploredMissed;
class TraceAnnotation;
class TraceAlert;
class TraceDomModification;
class TracePageLoad;
class TraceMarker;
class TraceFunctionCall;
class TraceEnd;
class TraceEndSuccess;
class TraceEndFailure;
class TraceEndUnknown;


/*
 *  The visitor interface.
 *  Implementations of this interface must implement visit() at least for TraceBranch but can also choose to
 *  implement special cases for specific node types as desired.
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

class TraceVisitor
{
public:
    // Must be provided by a concrete visitor as a catch-all.
    virtual void visit(TraceNode* node) = 0;

    // Supply a default implementation for each node type which relays the call to the node type's parent type.
    // These can be overrriden as required by a concrete visitor.
    virtual void visit(TraceBranch* node);
    virtual void visit(TraceConcreteBranch* node);
    virtual void visit(TraceSymbolicBranch* node);
    virtual void visit(TraceUnexplored* node);
    virtual void visit(TraceUnexploredUnsat* node);
    virtual void visit(TraceUnexploredUnsolvable* node);
    virtual void visit(TraceUnexploredMissed* node);
    virtual void visit(TraceAnnotation* node);
    virtual void visit(TraceAlert* node);
    virtual void visit(TraceDomModification* node);
    virtual void visit(TracePageLoad* node);
    virtual void visit(TraceMarker* node);
    virtual void visit(TraceFunctionCall* node);
    virtual void visit(TraceEnd* node);
    virtual void visit(TraceEndSuccess* node);
    virtual void visit(TraceEndFailure* node);
    virtual void visit(TraceEndUnknown* node);

    // Helper methods for concrete visitors.
    static bool isImmediatelyUnexplored(QSharedPointer<TraceNode> trace);
    static bool isImmediatelyUnsat(QSharedPointer<TraceNode> trace);
    static bool isImmediatelyConcreteBranch(QSharedPointer<TraceNode> trace);

    virtual ~TraceVisitor(){}
};

typedef QSharedPointer<TraceVisitor> TraceVisitorPtr;


} // namespace artemis

#endif // TRACEVISITOR_H
