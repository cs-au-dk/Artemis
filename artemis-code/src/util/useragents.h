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

#ifndef USERAGENTS_H
#define USERAGENTS_H

#include <QString>
#include <QMap>

namespace artemis
{

class UserAgents
{
public:
    static QMap<QString, QString> userAgents() {
        QMap<QString, QString> ua;
        ua.insert("default", "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/536.10 (KHTML, like Gecko) artemis Safari/536.10"); // N.B. may not be the default on other platforms!
        ua.insert("iphone4", "Mozilla/5.0 (iPhone; U; CPU iPhone OS 4_2_1 like Mac OS X; en-us) AppleWebKit/533.17.9 (KHTML, like Gecko) Version/5.0.2 Mobile/8C148 Safari/6533.18.5");
        ua.insert("ipad4", "Mozilla/5.0 (iPad; CPU OS 7_0 like Mac OS X) AppleWebKit/537.51.1 (KHTML, like Gecko) Version/7.0 Mobile/11A465 Safari/9537.53");
        ua.insert("nexus5", "Mozilla/5.0 (Linux; Android 4.2.1; en-us; Nexus 5 Build/JOP40D) AppleWebKit/535.19 (KHTML, like Gecko) Chrome/18.0.1025.166 Mobile Safari/535.19");
        ua.insert("chrome35", "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/35.0.1916.114 Safari/537.36");
        return ua;
        // Please update the help text in artemis.cpp when these are changed!
    }
};



} // namespace artemis
#endif // USERAGENTS_H
