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

#ifndef NULLCLASSIFIER_H
#define NULLCLASSIFIER_H

#include <QSharedPointer>

#include "concolic/executiontree/classifier/traceclassifier.h"


namespace artemis
{


/*
 *  Performs no classification - traces are returned with no modification.
 */
class NullClassifier : public TraceClassifier
{
public:
    NullClassifier();

    TraceClassificationResult classify(TraceNodePtr &trace);

protected:
    // Catch-all. Should not be called.
    void visit(artemis::TraceNode*);
};



} // namespace artemis

#endif // NULLCLASSIFIER_H
