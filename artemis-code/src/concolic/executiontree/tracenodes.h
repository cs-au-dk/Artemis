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

/*
 *  The various types of trace node which are used.
 *  These are used both for recording a single trace and the nodes in the path tree.
 *
 *  A single trace is jsut a sequence of TraceNodes.
 *  TraceBranch nodes come from the WebKit instrumentation.
 *  TraceAnnotation nodes come from the "interesting event detectors".
 *      They are used by the classifier and must be ignored by the search algorithm.
 *  TraceEnd nodes are added by the classifier and used by the search algorithm.
 *  TraceUnexplored nodes are only used in the path tree and
 *
 *  We also have a visitor interface to allow these traces (and trees) to be explored.
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

#include "nodes/trace.h"
#include "nodes/tracebranch.h"
#include "nodes/traceconcretebranch.h"
#include "nodes/tracesymbolicbranch.h"
#include "nodes/traceunexplored.h"
#include "nodes/traceunexploredunsat.h"
#include "nodes/traceunexploredunsolvable.h"
#include "nodes/traceunexploredmissed.h"
#include "nodes/traceunexploredqueued.h"

#ifndef TRACENODES_H
#define TRACENODES_H

#endif // TRACENODES_H
