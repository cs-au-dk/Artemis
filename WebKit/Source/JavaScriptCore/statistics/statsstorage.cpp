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

#include "statsstorage.h"

#include <QDebug>
#include <iostream>

#ifdef ARTEMIS


namespace Statistics
{

StatsStorage::StatsStorage()
{
}

void StatsStorage::accumulate(const std::string& key, int value)
{
    IntStorage::iterator iter = mIntStorage.find(key);

    if (iter == mIntStorage.end()) {
        mIntStorage.insert(std::pair<std::string, int>(key, value));
    } else {
        iter->second += value;
    }
}

void StatsStorage::accumulate(const std::string& key, double value)
{
    DoubleStorage::iterator iter = mDoubleStorage.find(key);

    if (iter == mDoubleStorage.end()) {
        mDoubleStorage.insert(std::pair<std::string, double>(key, value));
    } else {
        iter->second += value;
    }
}

void StatsStorage::set(const std::string& key, int value)
{
    mIntStorage.insert(std::pair<std::string, int>(key, value));
}

void StatsStorage::set(const std::string& key, bool value)
{
    mStringStorage.insert(std::pair<std::string, std::string>(key, (value ? "true" : "false")));
}

void StatsStorage::set(const std::string& key, double value)
{
    mDoubleStorage.insert(std::pair<std::string, double>(key, value));
}

void StatsStorage::set(const std::string& key, const std::string& value)
{
    mStringStorage.insert(std::pair<std::string, std::string>(key, value));
}

void StatsStorage::writeToStdOut()
{

    IntStorage::iterator iiter = mIntStorage.begin();

    while (iiter != mIntStorage.end()) {
        std::cout << iiter->first << ": " << iiter->second << std::endl;
        iiter++;
    }

    StringStorage::iterator siter = mStringStorage.begin();

    while (siter != mStringStorage.end()) {
        std::cout << siter->first << ": " << siter->second << std::endl;
        siter++;
    }

    DoubleStorage::iterator diter = mDoubleStorage.begin();

    while (diter != mDoubleStorage.end()) {
        std::cout << diter->first << ": " << diter->second << std::endl;
        diter++;
    }

}


StatsStorage* statistics()
{
    static StatsStorage instance;
    return &instance;
}

}
#endif
