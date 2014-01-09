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

#include <assert.h>
#include <QDebug>

#include "mockentrypointdetector.h"

namespace artemis
{


MockEntryPointDetector::MockEntryPointDetector(ArtemisWebPagePtr page) :
    EntryPointDetector(page)
{
}

EventHandlerDescriptorConstPtr MockEntryPointDetector::choose(ExecutionResultPtr result)
{

    // Detect all entry points on the page, according to the heuristics in detectAll().
    QList<EventHandlerDescriptorConstPtr> allEntryPoints = detectAll(result);

    // If we found none, return null.
    if(allEntryPoints.empty()){
        qDebug() << "Could not detect any entry points.\n";
        // TODO, we should really not do this... could we throw an exception?
        return EventHandlerDescriptorConstPtr();
    }



    // For local testing of the examples, we fall back to the standard behaviour of selecting the first entry point.
    if(mPage->currentFrame()->url().host() == "localhost"){
        return allEntryPoints.at(0);
    }

    // Special cases for particular sites, where we have manually selected the correct entry point.
    // The assertion on the total number of entry points is designed to catch any changes to the entry point
    // finding function from entrypoints.cpp which may affect these choices.

    QString url = mPage->currentFrame()->url().toString();

    if(url == "http://www.airtran.com/Home.aspx"){
        assert(allEntryPoints.length() == 11);
        return allEntryPoints.at(5);
        // 4 is the href on the button
        // 5 is the onclick of the same button
        // 9 is the form submission event for the "flight status" form (not the main search form)
    }

    if(url == "http://www.flykingfisher.com/"){
        assert(allEntryPoints.length() == 5);
        return allEntryPoints.at(1);
    }

    if(url == "http://www.jetstar.com/au/en/home"){
        assert(allEntryPoints.length() == 61);
        return allEntryPoints.at(5);
    }

    if(url == "http://www.monarch.co.uk/"){
        assert(allEntryPoints.length() == 34);
        return allEntryPoints.at(7);
    }

    if(url == "http://www.usairways.com/default.aspx"){
        assert(allEntryPoints.length() == 51);
        return allEntryPoints.at(18);
    }

    if(url == "http://www.southwest.com/"){
        assert(allEntryPoints.length() == 18);
        return allEntryPoints.at(14);
        // could also be 8, which is the form submission event.
    }

    if(url == "http://www.travelocity.co.uk/?WAPageName=HPGEOREDIRECT.UNITEDKINGDOM"){
        assert(allEntryPoints.length() == 8);
        return allEntryPoints.at(5);
        // Could also be 4, which is the form submission event.
    }

    if(url == "http://www.virginaustralia.com/au/en/"){
        assert(allEntryPoints.length() == 11);
        return allEntryPoints.at(8);
    }

    if(url == "http://www.united.com/web/en-US/default.aspx?root=1"){
        assert(allEntryPoints.length() == 54);
        return allEntryPoints.at(14);
    }

    if(url == "http://www.emirates.com/uk/english/index.aspx"){
        assert(allEntryPoints.length() == 979);
        return allEntryPoints.at(23);
    }

    if(url == "http://www.lufthansa.com/online/portal/lh/uk/homepage?l=en"){
        assert(allEntryPoints.length() == 34);
        return allEntryPoints.at(14);
    }

    if(url == "http://www.alaskaair.com/"){
        assert(allEntryPoints.length() == 19);
        return allEntryPoints.at(10);
    }

    if(url == "http://www.jetblue.com/"){
        assert(allEntryPoints.length() == 26);
        return allEntryPoints.at(16);
    }

    if(url == "http://www.flyfrontier.com/"){
        assert(allEntryPoints.length() == 23);
        return allEntryPoints.at(1);
    }


    qDebug() << "Did not match any known URL during entry-point finding.";
    qDebug() << "URL: " << url;
    qDebug() << "Candidate EPs: " << allEntryPoints.length();

    // If the site is not on the list, then this mock class does not support it, just return something
    // Most of our tests expect this behaviour
    return allEntryPoints.at(0);

}




} // namespace artemis
