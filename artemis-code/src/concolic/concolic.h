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




class ConcolicAnalysis
{
public:
    ConcolicAnalysis(bool demoMode);

    void run();

private:
    bool mDemoMode;
    //EntryPointDetector mEntryPointDetector;

};


typedef QSharedPointer<ConcolicAnalysis> ConcolicAnalysisPtr;





} // namespace artemis


#endif // CONCOLIC_H
