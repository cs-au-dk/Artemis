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

#include <iostream>
#include <QString>

#include <QDebug>

#include "util/loggingutil.h"
#include "pretty.h"

namespace artemis
{

StatsPrettyWriter::StatsPrettyWriter() {}

void StatsPrettyWriter::write(const StatsStorage* stats)
{

    QHashIterator<QString, int> i(stats->intStorage);

    while (i.hasNext()) {
        i.next();
        Log::info(i.key().toStdString()+": "+QString::number(i.value()).toStdString());
    }

    QHashIterator<QString, QString> j(stats->stringStorage);

    while (j.hasNext()) {
        j.next();
        Log::info(j.key().toStdString()+": "+j.value().toStdString());
    }

    QHashIterator<QString, double> k(stats->doubleStorage);

    while (k.hasNext()) {
        k.next();
        Log::info(k.key().toStdString()+": "+QString::number(k.value()).toStdString());
    }

}

}
