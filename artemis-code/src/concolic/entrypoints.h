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

#include <QString>
#include <QList>
#include <QWebFrame>

#include "runtime/browser/executionresult.h"

#ifndef ENTRYPOINTS_H
#define ENTRYPOINTS_H

namespace artemis
{




/*
 *  Inspects the page to detect any entry points (i.e. forms and buttons) we may wish to analyse.
 *  Assumes Artemis is running with a page loaded.
 */

class EntryPointDetector
{
public:
    EntryPointDetector(ArtemisWebPagePtr page);

    QList<EventHandlerDescriptorConstPtr> detectAll(ExecutionResultPtr result);

    // Chooses a single entry point on the page. Can return NULL if it does not find a suitable entry point.
    EventHandlerDescriptorConstPtr choose(ExecutionResultPtr result);

protected:
    ArtemisWebPagePtr mPage;
    void printResultInfo(ExecutionResultPtr result);
};



}


#endif // ENTRYPOINTS_H
