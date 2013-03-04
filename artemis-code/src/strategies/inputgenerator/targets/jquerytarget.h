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
#ifndef JQUERYTARGET_H
#define JQUERYTARGET_H

#include <QWebElement>

#include "strategies/inputgenerator/targets/jquerylistener.h"
#include "targetdescriptor.h"

namespace artemis
{

class JQueryTarget : public TargetDescriptor
{
public:
    JQueryTarget(QObject* parent, const EventHandlerDescriptor* eventHandler, JQueryListener* jqueryListener);

    QWebElement get(ArtemisWebPagePtr page) const;

protected:
    QString getSignature(QWebElement element) const;
    JQueryListener* mJQueryListener;
};

}

#endif
