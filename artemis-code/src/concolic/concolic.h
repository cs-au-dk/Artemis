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

#include <QSharedPointer>

#include "entrypoints.h"


#ifndef CONCOLIC_H
#define CONCOLIC_H

namespace artemis
{


/*
 *  The main controller for the concolic execution.
 *
 *  Algorithm:
 *      Run initial trace (insert into empty path tree)
 *      While not finished do:
 *          Search algorithm chooses a desired path
 *          Retrieve the coresponding path constraint (from path tree)
 *          Solve the constraint, returns a concrete input to test
 *              * Need to deal with cases where we can't solve (simplest implementation: mark as given up and move on)
 *          Execute the program on the new concrete input
 *          Build an annotated trace of the path taken
 *          Classify the trace as a success/failure and add it to the tree
 *          Check that we took the intended path
 *              * Need to deal with cases where we did not (simplest implementation: just give up)
 *          Finish after some condition (coverage, timeout, ...)
 *      od
 *
 *
 *  We also have a demo mode which does not drive the execution but only records and prints out the information
 *  which would be collected during a run of concolic execution.
 *
 */

class ConcolicAnalysis
{
public:
    ConcolicAnalysis(bool demoMode);

    void run();

private:
    bool mDemoMode;
    EntryPointDetector mEntryPointDetector;

};


typedef QSharedPointer<ConcolicAnalysis> ConcolicAnalysisPtr;





} // namespace artemis


#endif // CONCOLIC_H
