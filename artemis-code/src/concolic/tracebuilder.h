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

#ifndef TRACEBUILDER_H
#define TRACEBUILDER_H


/*
 *  Builds annotated traces of a given execution on a particular input.
 */

class TraceBuilder
{

};



/*
 *  Detectors listen for different interesting events and report them to the TraceBuilder.
 */

class TraceEventDetector
{

};



/*
 *  Below are the specific detectors we will use to build our traces.
 */

class BranchDetector : TraceEventDetector
{

};

// TODO: How is this handled? Should it actually be dealt with by the TraceBuilder itself?
class EndOfExecutionDetector : TraceEventDetector
{

};

class AlertDetector : TraceEventDetector
{

};

class DOMModificationDetector : TraceEventDetector
{

};

class PageChangeDetector : TraceEventDetector
{

};



#endif // TRACEBUILDER_H
