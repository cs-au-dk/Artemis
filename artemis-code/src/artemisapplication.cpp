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

#include "runtime/runtime.h"

#include "artemisapplication.h"

using namespace std;

namespace artemis
{

ArtemisApplication::ArtemisApplication(QObject* parent,
                                       QCoreApplication* qapp,
                                       const Options& options,
                                       QUrl url) :
    QObject(parent)
{
    this->app = qapp;

    srand(0); //Better way to get random numbers?

    mRuntime = new Runtime(this, options, url);

    QObject::connect(mRuntime, SIGNAL(sigTestingDone()),
                     this, SLOT(slTestingDone()));
}

void ArtemisApplication::run(QUrl url)
{
    mRuntime->startAnalysis(url);
}

void ArtemisApplication::slTestingDone()
{
    app->quit();
}
}
