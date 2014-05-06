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

#include <map>
#include <string>

#ifdef ARTEMIS

namespace Statistics
{

class StatsStorage
{

public:
    StatsStorage();

    void accumulate(const std::string& key, int value);
    void accumulate(const std::string& key, double value);
    void set(const std::string& key, int value);
    void set(const std::string& key, bool value);
    void set(const std::string& key, double value);
    void set(const std::string& key, const std::string& value);

    void writeToStdOut();

private:
    typedef std::map<std::string, int> IntStorage;
    typedef std::map<std::string, double> DoubleStorage;
    typedef std::map<std::string, std::string> StringStorage;

    IntStorage mIntStorage;
    DoubleStorage mDoubleStorage;
    StringStorage mStringStorage;
};

StatsStorage* statistics();

}

#endif //ARTEMIS
#endif // STATSSTORAGE_H
