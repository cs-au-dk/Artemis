#ifndef APPMODEL_H
#define APPMODEL_H

#include "coverage/coveragelistener.h"

namespace artemis {

class AppModel
{

public:
    AppModel(CoverageListener* coverageListener);

    CoverageListener* getCoverageListener() const;

private:
    CoverageListener* mCoverageListener;

};

}

#endif // APPMODEL_H
