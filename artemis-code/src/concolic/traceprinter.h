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

#include <QStack>
#include <QList>
#include <QString>

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
    void visit(TraceNode* node);
};


class CompleteTracePrintingVisitor : public TraceVisitor
{
public:
    void visit(TraceNode* node);
    void visit(TraceBranch* node);
    void visit(TraceUnexplored* node);
    void visit(TraceAlert* node);
    void visit(TraceDomModification* node);
    void visit(TracePageLoad* node);
    void visit(TraceEndSuccess* node);
    void visit(TraceEndFailure* node);
    void visit(TraceEndUnknown* node);
};


class SearchStylePrintingVisitor : public TraceVisitor
{
public:
    void visit(TraceNode* node);
    void visit(TraceBranch* node);
    void visit(TraceUnexplored* node);
    void visit(TraceAnnotation* node);
    void visit(TraceEndSuccess* node);
    void visit(TraceEndFailure* node);
    void visit(TraceEndUnknown* node);
};



/*
 *  Here is a "real" visitor which can be used to print an entire trace or tree onto the terminal.
 */
class TerminalTracePrinter : public TraceVisitor
{
public:
    TerminalTracePrinter();

    void visit(TraceNode* node); // Never called unless node types change.
    void visit(TraceBranch* node);
    void visit(TraceUnexplored* node);
    void visit(TraceAlert* node);
    void visit(TraceDomModification* node);
    void visit(TracePageLoad* node);
    void visit(TraceEndSuccess* node);
    void visit(TraceEndFailure* node);
    void visit(TraceEndUnknown* node);

    void printTraceTree(TraceNodePtr root);

private:
    struct PrintableTree
    {
        PrintableTree():width(0),connector(0){}
        void clear(){width=0;connector=0;lines.clear();}
        QList<QString> lines;
        int width;
        int connector;
    };
    PrintableTree mCurrentTree;
    QStack<PrintableTree> mCompletedLeftTrees;
    void addSingleValue(QString nodeText);
    void addBranch(QString nodeText);
    static QString padToConnector(QString text, int connector, int width);

};

} // namespace artemis


#endif // TRACEPRINTER_H
