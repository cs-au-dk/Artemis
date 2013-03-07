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
#ifndef APPMODEL_H
#define APPMODEL_H

#include <QSharedPointer>
#include <QUrl>

#include "model/coverage/coveragelistener.h"
#include "model/javascriptstatistics.h"

namespace artemis {

class AppModel
{

public:
    AppModel(QSet<QUrl> coverageIgnoredUrls);

    CoverageListenerPtr getCoverageListener() const;
    JavascriptStatisticsPtr getJavascriptStatistics() const;

private:
    CoverageListenerPtr mCoverageListener;
    JavascriptStatisticsPtr mJavascriptStatistics;

};

typedef QSharedPointer<AppModel> AppModelPtr;
typedef QSharedPointer<const AppModel> AppModelConstPtr;
}

#endif // APPMODEL_H
