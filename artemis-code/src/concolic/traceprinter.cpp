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



void VeryBoringTracePrintingVisitor::visit(TraceNode* node)
{
    Log::info("VBTP: At a NODE.");
}



//---------------------------------------------------------------------------//



void CompleteTracePrintingVisitor::visit(TraceNode* node)
{
    Log::info("CTPV: At a NODE. THIS SHOULD NEVER BE REACHED!");
}

void CompleteTracePrintingVisitor::visit(TraceBranch* node)
{
    Log::info("CTPV: At a BRANCH.");
}

void CompleteTracePrintingVisitor::visit(TraceUnexplored* node)
{
    Log::info("CTPV: At an UNEXPLORED.");
}

void CompleteTracePrintingVisitor::visit(TraceAlert* node)
{
    Log::info("CTPV: At an ALERT.");
}

void CompleteTracePrintingVisitor::visit(TraceDomModification* node)
{
    Log::info("CTPV: At a DOM CHANGE.");
}

void CompleteTracePrintingVisitor::visit(TracePageLoad* node)
{
    Log::info("CTPV: At a PAGE LOAD.");
}

void CompleteTracePrintingVisitor::visit(TraceEndSuccess* node)
{
    Log::info("CTPV: At an END SUCCESS.");
}

void CompleteTracePrintingVisitor::visit(TraceEndFailure* node)
{
    Log::info("CTPV: At an END FAIL.");
}

void CompleteTracePrintingVisitor::visit(TraceEndUnknown* node)
{
    Log::info("CTPV: At an END UNK.");
}



//---------------------------------------------------------------------------//





void SearchStylePrintingVisitor::visit(TraceNode* node)
{
    Log::info("SSPV: At a NODE. SHOULD NOT BE REACHABLE.");
}

void SearchStylePrintingVisitor::visit(TraceBranch* node)
{
    Log::info("SSPV: At a BRANCH.");
}

void SearchStylePrintingVisitor::visit(TraceUnexplored* node)
{
    Log::info("SSPV: At an UNEXPLORED.");
}

void SearchStylePrintingVisitor::visit(TraceAnnotation* node)
{
    Log::info("SSPV: At an ANNOTATION (of some kind).");
}

void SearchStylePrintingVisitor::visit(TraceEndSuccess* node)
{
    Log::info("SSPV: At an END SUCCESS.");
}

void SearchStylePrintingVisitor::visit(TraceEndFailure* node)
{
    Log::info("SSPV: At an ENS FAILURE.");
}

void SearchStylePrintingVisitor::visit(TraceEndUnknown* node)
{
    Log::info("SSPV: At an END UNK.");
}



//---------------------------------------------------------------------------//





} // namespace artemis

