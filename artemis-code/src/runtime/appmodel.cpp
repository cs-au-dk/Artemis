#include "appmodel.h"

#include <QObject>

namespace artemis {

AppModel::AppModel(QObject* parent) :
    QObject(parent),
    mCoverageListener(new CoverageListener(this)),
    mJavascriptStatistics(new JavascriptStatistics(this))
{
}

CoverageListener* AppModel::getCoverageListener() const
{
    return mCoverageListener;
}

JavascriptStatistics* AppModel::getJavascriptStatistics() const
{
    return mJavascriptStatistics;
}

}
