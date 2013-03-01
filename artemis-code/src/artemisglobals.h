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
#ifndef ARTEMISGLOBALS_H
#define ARTEMISGLOBALS_H

#include <QtWebKit>

using namespace std;

namespace artemis
{

const QWebElement NULL_WEB_ELEMENT;
const QUrl DONT_MEASURE_COVERAGE("http://this-is-fake-dont-do-coverage.fake");

inline QString quoteString(const QString s)
{
    return "\"" + s + "\"";
}

inline QString boolTostring(const bool b)
{
    return (b ? "true" : "false");
}

inline QString intTostring(const int i)
{
    QString res = "";
    res.setNum(i);
    return res;
}

inline bool isOmit(const QUrl& u)
{
    //TODO add support for exclusion of libraries!
    return u == DONT_MEASURE_COVERAGE;
}

}

#endif // ARTEMISGLOBALS_H
