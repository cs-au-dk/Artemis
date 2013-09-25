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

#ifndef STATSSTORAGE_H
#define STATSSTORAGE_H

#include <QHash>

namespace artemis
{

class StatsStorage
{

    friend class StatsPrettyWriter;

public:
    StatsStorage();
    void accumulate(QString key, int value);
    void set(QString key, int value);
    void set(QString key, bool value);
    void set(QString key, QString value);
    void set(QString key, const std::string& value);

private:
    QHash<QString, int> intStorage;
    QHash<QString, QString> stringStorage;
};

StatsStorage* statistics();

}

#endif // STATSSTORAGE_H
