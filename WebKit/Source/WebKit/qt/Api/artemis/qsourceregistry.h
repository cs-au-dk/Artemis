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

#ifndef QSOURCEREGISTRY_H
#define QSOURCEREGISTRY_H

#include <qwebkitglobal.h>

#include <QString>
#include <QPair>
#include <QHash>

#include "qsource.h"

namespace JSC {
    class SourceProvider;
}

class QSourceRegistry
{

public:
    QSourceRegistry();

    // <url, lineoffset>
    //QPair<QString, uint> getLocation(sourceid_t sourceID) const;
    QSource* get(JSC::SourceProvider* sourceProvider);

private:
    //QHash<JSC::SourceProvider*, sourceid_t> m_registry;

    JSC::SourceProvider* m_cache_key;
    QSource* m_cache_source;

    QHash<uint, QSource*> m_registry;


};

#endif // QSOURCEREGISTRY_H
