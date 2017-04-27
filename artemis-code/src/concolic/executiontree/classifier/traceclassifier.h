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

#ifndef TRACECLASSIFIER_H
#define TRACECLASSIFIER_H

#include <QSharedPointer>

#include "concolic/executiontree/tracenodes.h"
#include "concolic/executiontree/tracevisitor.h"


namespace artemis
{


enum TraceClassificationResult {
    UNKNOWN, SUCCESS, FAILURE
};


/*
 *  Classifies a complete annotated trace as either a success or a failure.
 *  Also modifies the trace to include an END-SUCCESS or END-FAILURE marker.
 */
class TraceClassifier : public TraceVisitor
{
public:
    virtual TraceClassificationResult classify(TraceNodePtr &trace) = 0;
};

typedef QSharedPointer<TraceClassifier> TraceClassifierPtr;





} // namespace artemis

#endif // TRACECLASSIFIER_H
