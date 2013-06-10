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

#include "concolicruntime.h"

#include "util/loggingutil.h"

namespace artemis
{


ConcolicRuntime::ConcolicRuntime(QObject* parent, const Options& options, const QUrl& url) :
    Runtime(parent, options, url)
{
    Log::fatal("Fully automatic concolic execution is not yet implemented.");
    Log::fatal("Try 'manual' mode for a demo of some of the symbolic features.");
    exit(1);
}



void ConcolicRuntime::run(const QUrl& url)
{


}



} // namespace artemis

