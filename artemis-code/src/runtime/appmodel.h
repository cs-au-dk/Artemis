#ifndef APPMODEL_H
#define APPMODEL_H

#include <QSharedPointer>

#include "coverage/coveragelistener.h"
#include "runtime/model/javascriptstatistics.h"

namespace artemis {

class AppModel
{

public:
    AppModel();

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
