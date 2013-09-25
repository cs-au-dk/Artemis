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

#ifndef APPMODEL_H
#define APPMODEL_H

#include <QSharedPointer>

#include "runtime/options.h"
#include "model/coverage/coveragelistener.h"
#include "model/javascriptstatistics.h"
#include "model/pathtracer.h"

namespace artemis {

class AppModel
{

public:
    AppModel(Options options);

    CoverageListenerPtr getCoverageListener() const;
    JavascriptStatisticsPtr getJavascriptStatistics() const;
    PathTracerPtr getPathTracer() const;

private:
    CoverageListenerPtr mCoverageListener;
    JavascriptStatisticsPtr mJavascriptStatistics;
    PathTracerPtr mPathTracer;

};

typedef QSharedPointer<AppModel> AppModelPtr;
typedef QSharedPointer<const AppModel> AppModelConstPtr;
}

#endif // APPMODEL_H
