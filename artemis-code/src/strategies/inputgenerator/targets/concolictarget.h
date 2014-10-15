/*
 * Copyright 2014 Aarhus University
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

#ifndef CONCOLICTARGET_H
#define CONCOLICTARGET_H

#include <QWebElement>

#include "strategies/inputgenerator/targets/jquerylistener.h"
#include "targetdescriptor.h"

namespace artemis
{

class ConcolicTarget : public TargetDescriptor
{
public:
    ConcolicTarget(EventHandlerDescriptorConstPtr eventHandler);
    QWebElement get(ArtemisWebPagePtr page) const;
};

}

#endif // CONCOLICTARGET_H
