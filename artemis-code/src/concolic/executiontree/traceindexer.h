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

#include "tracenodes.h"
#include "tracevisitor.h"

#ifndef TRACEINDEXER_H
#define TRACEINDEXER_H

namespace artemis
{



class TraceIndexer : public TraceVisitor
{
public:
    static void index(TraceNodePtr trace, uint index);

protected:
    TraceIndexer(uint index);
    uint mIndex;

    virtual void visit(TraceNode* node);
    virtual void visit(TraceBranch* node);
    virtual void visit(TraceUnexplored* node);
    virtual void visit(TraceAnnotation* node);
    virtual void visit(TraceConcreteSummarisation* node);
    virtual void visit(TraceEnd* node);
};


} // namespace artemis
#endif // TRACEINDEXER_H
