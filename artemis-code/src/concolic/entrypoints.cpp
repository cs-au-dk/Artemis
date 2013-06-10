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


#include "entrypoints.h"
#include "util/loggingutil.h"


namespace artemis
{



EntryPointDetector::EntryPointDetector()
{

}


QList<EventHandlerDescriptor*> EntryPointDetector::detectAll(ExecutionResultPtr result)
{
    // TEMP: for development...
    printResultInfo(result);

    // Build a list of potential entry points.

    // For now we have a very simple implementation which only checks any for 'click' events on 'button' inputs.
    // TODO: at least also 'submit' on 'form' and maybe check where these buttons are...

    QList<EventHandlerDescriptor*> entryEvents;

    foreach(EventHandlerDescriptor* event , result->getEventHandlers()){
        if(event->name().compare("click", Qt::CaseInsensitive) == 0 &&
                event->domElement()->getTagName().compare("button", Qt::CaseInsensitive) == 0){
            entryEvents.append(event);
        }
    }

    return entryEvents;
}



void EntryPointDetector::printResultInfo(ExecutionResultPtr result)
{
    Log::info("CONCOLIC-INFO: Detecting entry points on page.");

    // Begin by just listing some relevant information from the execution result...
    QString eventNames;
    foreach(EventHandlerDescriptor* event , result->getEventHandlers()){
        eventNames.append(QString("%1 on %2, ").arg(event->name()).arg(event->domElement()->getTagName()));
    }
    Log::info(QString("CONCOLIC-INFO: Event Handlers (%1): %2").arg(result->getEventHandlers().length()).arg(eventNames).toStdString());

    QString formNames;
    foreach(QSharedPointer<const FormField> field, result->getFormFields()){
        formNames.append(field->getDomElement()->getTagName());
        formNames.append(", ");
    }
    Log::info(QString("CONCOLIC-INFO: Form Fileds (%1): %2").arg(result->getFormFields().size()).arg(formNames).toStdString());

    Log::info(QString("CONCOLIC-INFO: Is DOM Modified: %1").arg(result->isDomModified() ? "Yes" : "No").toStdString());

}

}

