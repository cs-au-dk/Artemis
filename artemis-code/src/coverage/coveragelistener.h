/*
  Copyright 2011 Simon Holm Jensen. All rights reserved.

  Redistribution and use in source and binary forms, with or without modification, are
  permitted provided that the following conditions are met:

     1. Redistributions of source code must retain the above copyright notice, this list of
        conditions and the following disclaimer.

     2. Redistributions in binary form must reproduce the above copyright notice, this list
        of conditions and the following disclaimer in the documentation and/or other materials
        provided with the distribution.

  THIS SOFTWARE IS PROVIDED BY SIMON HOLM JENSEN ``AS IS'' AND ANY EXPRESS OR IMPLIED
  WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND
  FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL <COPYRIGHT HOLDER> OR
  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
  CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
  SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
  ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
  NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
  ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

  The views and conclusions contained in the software and documentation are those of the
  authors and should not be interpreted as representing official policies, either expressed
  or implied, of Simon Holm Jensen
*/
#ifndef COVERAGELISTENER_H
#define COVERAGELISTENER_H

#include <inttypes.h>

#include <QObject>
#include <QUrl>
#include <QMap>

#include "sourceinfo.h"
#include "lineinfo.h"
#include "codecoverage.h"

namespace artemis
{

class CoverageListener : public QObject
{
    Q_OBJECT
public:
    explicit CoverageListener(QObject* parent = 0);
    CodeCoverage currentCoverage();


private:
    // (Hash of startline + url -> SourceInfo)
    QMap<int, SourceInfo*> sources;
    // (Hash of startline + url -> Coverage information)
    QMap<int, QMap<int, LineInfo>* > coverage;
    // (Webkit source id -> Hash of startline + url)
    QMap<intptr_t, int> webkitPointers;



signals:

public slots:
    void newCode(intptr_t id, QString source, QUrl url, int startline);
    void statementExecuted(intptr_t sourceID, std::string functionName, int linenumber);
};

}

#endif // COVERAGELISTENER_H
