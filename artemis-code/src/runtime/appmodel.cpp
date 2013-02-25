#include "appmodel.h"

namespace artemis {

AppModel::AppModel(CoverageListener* coverageListener) :
    mCoverageListener(coverageListener)
{
}

CoverageListener* AppModel::getCoverageListener() const
{
    return mCoverageListener;
}

}
