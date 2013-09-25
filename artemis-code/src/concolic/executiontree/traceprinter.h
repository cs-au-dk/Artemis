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

#include "concolic/executiontree/tracenodes.h"

#include <QStack>
#include <QList>
#include <QMutableListIterator>
#include <QString>

#ifndef TRACEPRINTER_H
#define TRACEPRINTER_H


namespace artemis
{

/**
 *  A visitor for traces or trace trees which can print the tree to the terminal.
 *  Obviously this only works well on extremely small trees.
 */
class TerminalTracePrinter : public TraceVisitor
{
public:

    void visit(TraceNode* node); // Never called unless node types change.
    void visit(TraceConcreteBranch* node);
    void visit(TraceSymbolicBranch* node);
    void visit(TraceUnexplored* node);
    void visit(TraceAlert* node);
    void visit(TraceDomModification* node);
    void visit(TracePageLoad* node);
    void visit(TraceFunctionCall* node);
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
    void addSingleValue(QList<QString> nodeText);
    void addBranch(QString nodeText);
    void addBranch(QList<QString> nodeText);
    static QString padToConnector(QString text, int connector, int width);
    static QList<QString> processNodeTextLines(QList<QString> nodeText);

};

} // namespace artemis


#endif // TRACEPRINTER_H
