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


#include "tracevisitor.h"
#include "trace.h"

namespace artemis
{


// These "default" implementations simply relay the call top the parent class' method.
// They can be overriden as required to create a visitor of any granularity.
void TraceVisitor::visit(TraceBranch* node)             { visit(static_cast<TraceNode*>(node)); }
void TraceVisitor::visit(TraceUnexplored* node)         { visit(static_cast<TraceNode*>(node)); }
void TraceVisitor::visit(TraceAnnotation* node)         { visit(static_cast<TraceNode*>(node)); }
void TraceVisitor::visit(TraceAlert* node)              { visit(static_cast<TraceAnnotation*>(node)); }
void TraceVisitor::visit(TraceDomModification* node)    { visit(static_cast<TraceAnnotation*>(node)); }
void TraceVisitor::visit(TracePageLoad* node)           { visit(static_cast<TraceAnnotation*>(node)); }
void TraceVisitor::visit(TraceEnd* node)                { visit(static_cast<TraceNode*>(node)); }
void TraceVisitor::visit(TraceEndSuccess* node)         { visit(static_cast<TraceEnd*>(node)); }
void TraceVisitor::visit(TraceEndFailure* node)         { visit(static_cast<TraceEnd*>(node)); }
void TraceVisitor::visit(TraceEndUnknown* node)         { visit(static_cast<TraceEnd*>(node)); }



} // namespace artemis


