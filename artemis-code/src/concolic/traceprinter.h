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


#include "trace.h"


#ifndef TRACEPRINTER_H
#define TRACEPRINTER_H


namespace artemis
{


/*
 *  These three printing visitors are simply to test out the visitor functionality and make sure we can
 *  create visitors which work at different levels of abstraction. For example, the "search style" visitor below
 *  can treat all kinds of annotation the same, while the "complete" one differentiates them.
 */


class VeryBoringTracePrintingVisitor : public TraceVisitor
{
public:
    void visit(QSharedPointer<TraceNode> node);
};


class CompleteTracePrintingVisitor : public TraceVisitor
{
public:
    void visit(QSharedPointer<TraceNode> node);
    void visit(QSharedPointer<TraceBranch> node);
    void visit(QSharedPointer<TraceUnexplored> node);
    //void visit(QSharedPointer<TraceAnnotation> node);
    void visit(QSharedPointer<TraceAlert> node);
    void visit(QSharedPointer<TraceDomModification> node);
    void visit(QSharedPointer<TracePageLoad> node);
    //void visit(QSharedPointer<TraceEnd> node);
    void visit(QSharedPointer<TraceEndSuccess> node);
    void visit(QSharedPointer<TraceEndFailure> node);
    void visit(QSharedPointer<TraceEndUnknown> node);
};


class SearchStylePrintingVisitor : public TraceVisitor
{
public:
    void visit(QSharedPointer<TraceNode> node);
    void visit(QSharedPointer<TraceBranch> node);
    void visit(QSharedPointer<TraceUnexplored> node);
    void visit(QSharedPointer<TraceAnnotation> node);
    void visit(QSharedPointer<TraceEndSuccess> node);
    void visit(QSharedPointer<TraceEndFailure> node);
    void visit(QSharedPointer<TraceEndUnknown> node);
};


} // namespace artemis


#endif // TRACEPRINTER_H
