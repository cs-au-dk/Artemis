#ifndef APPMODEL_H
#define APPMODEL_H

#include "coverage/coveragelistener.h"
#include "runtime/model/javascriptstatistics.h"

namespace artemis {

class AppModel : public QObject
{

public:
    AppModel(QObject* parent);

    CoverageListener* getCoverageListener() const;
    JavascriptStatistics* getJavascriptStatistics() const;

private:
    CoverageListener* mCoverageListener;
    JavascriptStatistics* mJavascriptStatistics;

};

}

#endif // APPMODEL_H
