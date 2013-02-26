#include "appmodel.h"

#include <QObject>

namespace artemis {

AppModel::AppModel() :
    mCoverageListener(CoverageListenerPtr(new CoverageListener())),
    mJavascriptStatistics(JavascriptStatisticsPtr(new JavascriptStatistics()))
{
}

CoverageListenerPtr AppModel::getCoverageListener() const
{
    return mCoverageListener;
}

JavascriptStatisticsPtr AppModel::getJavascriptStatistics() const
{
    return mJavascriptStatistics;
}

}
