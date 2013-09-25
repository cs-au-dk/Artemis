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

#include "assert.h"
#include "randomutil.h"
#include <QSet>
#include <QDebug>

namespace artemis
{

QString generateRandomString(int length)
{
    static const char alphanum[] =
        "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";
    Q_ASSERT(length >= 0);

    if (length == 0)
        { return ""; }

    QString res;

    for (int i = 0; i < length; ++i)
        { res[i] = QChar(alphanum[rand() % (sizeof(alphanum) - 1)]); }

    return res;
}

bool randomBool()
{
    return (rand() % 100) > 50;
}

QWebElement pickRand(QList<QWebElement> s)
{
    assert(s.size()>0);
    if (s.size() == 1) {
        return s.at(0);
    }

    int elem = rand() % (s.size() - 1);
    return s.at(elem);
}

QString pickRand(QList<QString> s)
{
    if (s.size() == 1) {
        return s.at(0);
    }

    int elem = rand() % (s.size() - 1);
    assert(s.size()>0);
    return s.at(elem);
}

QString pickRand(QSet<QString> s)
{
    QList<QString> ll = s.toList();
    return pickRand(ll);
}

QString generateRandomJsId()
{
    return generateRandomString(5);
}

}
