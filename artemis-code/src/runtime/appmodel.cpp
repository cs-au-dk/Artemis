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

#include "appmodel.h"

#include <QObject>

namespace artemis {

AppModel::AppModel(Options options)
{
    mCoverageListener = CoverageListenerPtr(new CoverageListener(options.coverageIgnoreUrls ));
    mJavascriptStatistics = JavascriptStatisticsPtr(new JavascriptStatistics());

    // If we are in concolic mode then enable the path tracer by default (but without overriding any user-specified setting).
    if(options.majorMode == artemis::CONCOLIC && options.reportPathTrace == artemis::NO_TRACES){
        mPathTracer = PathTracerPtr(new PathTracer(artemis::HTML_TRACES, mCoverageListener));
    }else{
        mPathTracer = PathTracerPtr(new PathTracer(options.reportPathTrace, mCoverageListener));
    }
}

CoverageListenerPtr AppModel::getCoverageListener() const
{
    return mCoverageListener;
}

JavascriptStatisticsPtr AppModel::getJavascriptStatistics() const
{
    return mJavascriptStatistics;
}

PathTracerPtr AppModel::getPathTracer() const
{
    return mPathTracer;
}

}
