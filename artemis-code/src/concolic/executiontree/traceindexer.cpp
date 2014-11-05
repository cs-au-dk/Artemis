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

#include "traceindexer.h"

namespace artemis
{


void TraceIndexer::index(TraceNodePtr trace, uint index)
{
    TraceIndexer processor(index);
    trace->accept(&processor);
}


TraceIndexer::TraceIndexer(uint index)
    : mIndex(index)
{
}


void TraceIndexer::visit(TraceNode *node)
{
    Log::fatal("Trace Indexer: visited a node which was not handled correctly.");
    exit(1);
}

void TraceIndexer::visit(TraceBranch *node)
{
    node->getFalseBranch()->accept(this);
    node->getTrueBranch()->accept(this);
}

void TraceIndexer::visit(TraceUnexplored *node)
{
    return;
}

void TraceIndexer::visit(TraceAnnotation *node)
{
    node->next->accept(this);
}

void TraceIndexer::visit(TraceConcreteSummarisation *node)
{
    foreach(TraceConcreteSummarisation::SingleExecution execution, node->executions) {
        execution.second->accept(this);
    }
}

void TraceIndexer::visit(TraceEnd *node)
{
    node->traceIndices.insert(mIndex);
}


} //namespace artemis
