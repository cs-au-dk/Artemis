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

namespace artemis
{

StatsStorage::StatsStorage()
{
}

void StatsStorage::accumulate(QString key, int value)
{
    value += this->intStorage.value(key, 0);
    this->intStorage.insert(key, value);
}

void StatsStorage::set(QString key, int value)
{
    this->intStorage.insert(key, value);
}

void StatsStorage::set(QString key, bool value)
{
    this->stringStorage.insert(key, value ? "true" : "false");
}

void StatsStorage::set(QString key, QString value)
{
    this->stringStorage.insert(key, value);
}

void StatsStorage::set(QString key, const std::string& value)
{
    this->stringStorage.insert(key, value.c_str());
}

StatsStorage* statistics()
{
    static StatsStorage instance;
    return &instance;
}

}
