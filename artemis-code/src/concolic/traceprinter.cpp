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


#include "traceprinter.h"
#include "util/loggingutil.h"


namespace artemis
{




//---------------------------------------------------------------------------//



void VeryBoringTracePrintingVisitor::visit(QSharedPointer<TraceNode> node)
{
    Log::info("At a NODE.");
}



//---------------------------------------------------------------------------//



void CompleteTracePrintingVisitor::visit(QSharedPointer<TraceNode> node)
{
    Log::info("At a NODE. THIS SHOULD NEVER BE REACHED!");
}

void CompleteTracePrintingVisitor::visit(QSharedPointer<TraceBranch> node)
{
    Log::info("At a BRANCH.");
}

void CompleteTracePrintingVisitor::visit(QSharedPointer<TraceUnexplored> node)
{
    Log::info("At an UNEXPLORED.");
}

void CompleteTracePrintingVisitor::visit(QSharedPointer<TraceAlert> node)
{
    Log::info("At an ALERT.");
}

void CompleteTracePrintingVisitor::visit(QSharedPointer<TraceDomModification> node)
{
    Log::info("At a DOM CHANGE.");
}

void CompleteTracePrintingVisitor::visit(QSharedPointer<TracePageLoad> node)
{
    Log::info("At a PAGE LOAD.");
}

void CompleteTracePrintingVisitor::visit(QSharedPointer<TraceEndSuccess> node)
{
    Log::info("At an END SUCCESS.");
}

void CompleteTracePrintingVisitor::visit(QSharedPointer<TraceEndFailure> node)
{
    Log::info("At an END FAIL.");
}

void CompleteTracePrintingVisitor::visit(QSharedPointer<TraceEndUnknown> node)
{
    Log::info("At an END UNK.");
}



//---------------------------------------------------------------------------//





void SearchStylePrintingVisitor::visit(QSharedPointer<TraceNode> node)
{
    Log::info("At a NODE. SHOULD NOT BE REACHABLE.");
}

void SearchStylePrintingVisitor::visit(QSharedPointer<TraceBranch> node)
{
    Log::info("At a BRANCH.");
}

void SearchStylePrintingVisitor::visit(QSharedPointer<TraceUnexplored> node)
{
    Log::info("At an UNEXPLORED.");
}

void SearchStylePrintingVisitor::visit(QSharedPointer<TraceAnnotation> node)
{
    Log::info("At an ANNOTATION (of some kind).");
}

void SearchStylePrintingVisitor::visit(QSharedPointer<TraceEndSuccess> node)
{
    Log::info("At an END SUCCESS.");
}

void SearchStylePrintingVisitor::visit(QSharedPointer<TraceEndFailure> node)
{
    Log::info("At an ENS FAILURE.");
}

void SearchStylePrintingVisitor::visit(QSharedPointer<TraceEndUnknown> node)
{
    Log::info("At an END UNK.");
}



//---------------------------------------------------------------------------//





} // namespace artemis

