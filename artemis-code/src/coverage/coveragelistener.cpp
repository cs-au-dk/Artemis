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

#include "artemisglobals.h"
#include "util/urlutil.h"
#include "statistics/statsstorage.h"

#include "coveragelistener.h"

#include "util/loggingutil.h"
namespace artemis
{

CoverageListener::CoverageListener(QObject* parent) :
    QObject(parent)
{
}

CodeCoverage CoverageListener::currentCoverage()
{

    QMap<int, SourceInfo*> newSources;

    QMapIterator<int, SourceInfo*> sourcesIter(sources);

    while (sourcesIter.hasNext()) {
        sourcesIter.next();
        newSources.insert(sourcesIter.key(), new SourceInfo(NULL, sourcesIter.value()));
    }

    QMap<int, QMap<int, LineInfo> > newCoverage;

    QMapIterator<int, QMap<int, LineInfo>* > coverageIter(coverage);

    while (coverageIter.hasNext()) {
        coverageIter.next();
        newCoverage.insert(coverageIter.key(), *coverageIter.value());
    }

    return CodeCoverage(newSources, newCoverage);
}



void CoverageListener::newCode(intptr_t id, QString source, QUrl url, int startline)
{
    if (isOmit(url)) {
        return;
    }

    int hash = getHash(url, startline);
    webkitPointers.insert(id, hash);

    if (!sources.contains(hash)) {
        qDebug() << "Loaded new code: " << url << " at line " << QString::number(startline);
        SourceInfo* infoP = new SourceInfo(this, source, url, startline);
        sources.insert(hash, infoP);
        coverage.insert(hash, new QMap<int, LineInfo>());
    }
}



void CoverageListener::statementExecuted(intptr_t sourceID, std::string functionName, int linenumber)
{
    statistics()->accumulate("WebKit::coverage::covered", 1);

    int hash = webkitPointers[sourceID];
    QMap<int, LineInfo>* map = coverage.value(hash, 0);

    if (map == 0) {
        map = new QMap<int, LineInfo>();
    }

    coverage.insert(hash, map);

    if (map->contains(linenumber)) {
        LineInfo p = map->value(hash);
        p.lineExecuted();
        map->insert(linenumber, p);
    } else {
        LineInfo p;
        p.lineExecuted();
        map->insert(linenumber, p);
    }
}
}
