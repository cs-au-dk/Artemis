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

#include "statistics/statsstorage.h"
#include "util/loggingutil.h"

#include "entrypoints.h"

namespace artemis
{



EntryPointDetector::EntryPointDetector(ArtemisWebPagePtr page) :
    mPage(page)
{
}


QList<EventHandlerDescriptor*> EntryPointDetector::detectAll(ExecutionResultPtr result)
{
    // TEMP: for development...
    printResultInfo(result);

    // Build a list of potential entry points.

    // For now we have a simple implementation which checks for 'click' events on 'button' or 'a' elements.
    // TODO: at least also 'submit' on 'form' and maybe check where these buttons are...

    QList<EventHandlerDescriptor*> entryEvents;

    foreach(EventHandlerDescriptor* event , result->getEventHandlers()){
        if(event->name().compare("click", Qt::CaseInsensitive) == 0 &&
                event->domElement()->getTagName().compare("button", Qt::CaseInsensitive) == 0){
            // Accept any click on a button
            entryEvents.append(event);

        }else if(event->name().compare("click", Qt::CaseInsensitive) == 0 &&
                 event->domElement()->getTagName().compare("a", Qt::CaseInsensitive) == 0){

            // Accept a click on a link only if it is inside a form.
            QWebElement element = event->domElement()->getElement(mPage);
            // Search upwards until we find a form or reach the top of the hierarchy.
            while(element.tagName().compare("form", Qt::CaseInsensitive) != 0 &&
                  !element.isNull()){
                element = element.parent();
            }
            // If we did find a form element then we know the original event was on an element we consider interesting.
            if(element.tagName().compare("form", Qt::CaseInsensitive) == 0){
                entryEvents.append(event);
            }

        }else if(event->name().compare("click", Qt::CaseInsensitive) == 0 &&
                 event->domElement()->getTagName().compare("input", Qt::CaseInsensitive) == 0 &&
                 (event->domElement()->getElement(mPage).attribute("type").compare("button", Qt::CaseInsensitive) == 0 ||
                  event->domElement()->getElement(mPage).attribute("type").compare("submit", Qt::CaseInsensitive) == 0 ||
                  event->domElement()->getElement(mPage).attribute("type").compare("image", Qt::CaseInsensitive) == 0)){

            // Accept a click on an input element of type button, submit, or image.
            entryEvents.append(event);

        }

    }

    statistics()->accumulate("FormCrawl::Entrypoints", entryEvents.size());

    return entryEvents;
}



EventHandlerDescriptor *EntryPointDetector::choose(ExecutionResultPtr result)
{

    // Detect all entry points on the page, according to the heuristics in detectAll().
    QList<EventHandlerDescriptor*> allEntryPoints = detectAll(result);

    // If we found none, return null.
    if(allEntryPoints.empty()){
        return NULL;
    }

    // TODO: Temporary special case for airtran.com, choose the correct entry point (3rd one).
    QString url = mPage->currentFrame()->url().toString();
    if(url == "http://www.airtran.com/Home.aspx"){
        return allEntryPoints.at(2);
    }
    // TODO: Temporary special case for flykingfisher.com
    if(url == "http://www.flykingfisher.com/"){
        return allEntryPoints.at(1);
    }
    // TODO: Temporary special case for jetstar.com
    if(url == "http://www.jetstar.com/au/en/home"){
        return allEntryPoints.at(5);
    }
    // TODO: Temporary special case for monarch.co.uk
    if(url == "http://www.monarch.co.uk/"){
        return allEntryPoints.at(7);
    }
    // TODO: Temporary special case for usairways.com
    if(url == "http://www.usairways.com/default.aspx"){
        return allEntryPoints.at(13);
    }
    // TODO: Temporary special case for southwest.com
    if(url == "http://www.southwest.com/"){
        return allEntryPoints.at(9);
    }
    // TODO: Temporary special case for travelocity.co.uk
    if(url == "http://www.travelocity.co.uk/?WAPageName=HPGEOREDIRECT.UNITEDKINGDOM"){
        return allEntryPoints.at(3);
    }
    // TODO: Temporary special case for virginaustralia.com
    if(url == "http://www.virginaustralia.com/au/en/"){
        return allEntryPoints.at(4);
    }
    // TODO: Temporary special case for united.com
    if(url == "http://www.united.com/web/en-US/default.aspx?root=1"){
        return allEntryPoints.at(5);
    }
    // TODO: Temporary special case for united.com
    if(url == "http://www.emirates.com/uk/english/index.aspx"){
        return allEntryPoints.at(23);
    }

    // TODO: Trivial Choice: Choose the first entrypoint.
    return allEntryPoints.at(0);

}



void EntryPointDetector::printResultInfo(ExecutionResultPtr result)
{
    Log::debug("CONCOLIC-INFO: Detecting entry points on page.");

    // Begin by just listing some relevant information from the execution result...
    QString eventNames;
    foreach(EventHandlerDescriptor* event , result->getEventHandlers()){
        eventNames.append(QString("%1 on %2, ").arg(event->name()).arg(event->domElement()->getTagName()));
    }
    Log::debug(QString("CONCOLIC-INFO: Event Handlers (%1): %2").arg(result->getEventHandlers().length()).arg(eventNames).toStdString());

    QString formNames;
    foreach(QSharedPointer<const FormFieldDescriptor> field, result->getFormFields()){
        formNames.append(field->getDomElement()->getTagName());
        formNames.append(", ");
    }
    Log::debug(QString("CONCOLIC-INFO: Form Fileds (%1): %2").arg(result->getFormFields().size()).arg(formNames).toStdString());

    Log::debug(QString("CONCOLIC-INFO: Is DOM Modified: %1").arg(result->isDomModified() ? "Yes" : "No").toStdString());

}

}

