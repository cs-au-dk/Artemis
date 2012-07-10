#ifndef COVERAGEUTIL_H
#define COVERAGEUTIL_H


#include <QString>
#include "src/coverage/codecoverage.h"

namespace artemis {

    void write_coverage_html(QString filename, CodeCoverage cc);

}

#endif // COVERAGEUTIL_H
