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

#include "tracedisplay.h"

#ifndef TRACEDISPLAYOVERVIEW_H
#define TRACEDISPLAYOVERVIEW_H

namespace artemis
{


/**
 * Converts a trace or tree to GraphViz dot format.
 * The 'overview' graphs produced by this class are extremely simplified for
 * showing approximately how much has been explored in very large graphs.
 */
class TraceDisplayOverview : public TraceDisplay
{
public:
    TraceDisplayOverview();

    // The trace visitors
    //void visit(TraceNode* node);                  // Handled by TraceDisplay
    void visit(TraceConcreteBranch *node);
    void visit(TraceSymbolicBranch *node);
    //void visit(TraceUnexplored* node);            // Handled by TraceDisplay
    //void visit(TraceUnexploredUnsat* node);       // Handled by TraceDisplay
    //void visit(TraceUnexploredUnsolvable* node);  // Handled by TraceDisplay
    //void visit(TraceUnexploredMissed* node);      // Handled by TraceDisplay
    void visit(TraceAlert* node);
    void visit(TraceDomModification* node);
    void visit(TracePageLoad* node);
    void visit(TraceMarker* node);
    void visit(TraceFunctionCall* node);
    //void visit(TraceEndSuccess* node);            // Handled by TraceDisplay
    //void visit(TraceEndFailure* node);            // Handled by TraceDisplay
    //void visit(TraceEndUnknown* node);            // Handled by TraceDisplay

protected:

};


} //namespace artemis

#endif // TRACEDISPLAYOVERVIEW_H
