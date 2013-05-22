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


#ifndef CONCOLICDEMORUNTIME_H
#define CONCOLICDEMORUNTIME_H



#include <QObject>

#include "runtime/browser/artemiswebview.h"
#include "runtime/runtime.h"
#include "runtime/toplevel/manualruntime.h"

namespace artemis
{


/*
 *  The concolic demo runtime opens a GUI window (as in ManualRuntime) and also records and displays all the
 *  information used in the full concolic analysis.
 */

class ConcolicDemoRuntime : public ManualRuntime
{
    Q_OBJECT

public:
    ConcolicDemoRuntime(QObject* parent, const Options& options, const QUrl& url);

    void run(const QUrl& url);

protected:
    bool waitingForFirstLoad;

private:
    void concolicSetup();

private slots:
    void slPageLoadComplete(); // TODO: name? Does this exist somewhere already?

};




} // namespace artemis

#endif // CONCOLICDEMORUNTIME_H
