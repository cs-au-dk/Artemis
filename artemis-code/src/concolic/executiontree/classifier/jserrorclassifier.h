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

#ifndef JSERRORCLASSIFIER_H
#define JSERRORCLASSIFIER_H

#include <QSharedPointer>

#include "concolic/executiontree/classifier/traceclassifier.h"


namespace artemis
{


/*
 *  Classification is based on whether errors ocurred in the JavaScript code.
 *  We detect: alerts, console.error, console.assert (failed), unhandled JS exceptions.
 */
class JsErrorClassifier : public TraceClassifier
{
public:
    JsErrorClassifier();

    TraceClassificationResult classify(TraceNodePtr &trace);

protected:
    TraceClassificationResult mResult;

    // Catch-all. Should not be called.
    void visit(artemis::TraceNode*);

    // Certain annotation nodes are used in the classification
    virtual void visit(TraceAlert* node);
    virtual void visit(TraceConsoleMessage* node);
    // TODO: More annotation types to detect the errors we are interested in.

    // Catch-all for boring annotation types
    virtual void visit(TraceAnnotation* node);

    // Ignored for classification.
    virtual void visit(TraceBranch* node);
    virtual void visit(TraceConcreteSummarisation* node);

    // Should not be encountered on the main trace.
    virtual void visit(TraceUnexplored* node);

    // Traces should end with TraceEndUnknown nodes when they come from the trace builder.
    virtual void visit(TraceEndUnknown* node);

    // Catch-all for other end types (i.e. an error).
    virtual void visit(TraceEnd* node);
};



} // namespace artemis

#endif // JSERRORCLASSIFIER_H
