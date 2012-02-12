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
#include "coveragelistener.h"
#include "util/urlutil.h"
#include "artemisglobals.h"

namespace artemis {

    CoverageListener::CoverageListener(QObject *parent) :
            QObject(parent)
    {
    }

    CodeCoverage CoverageListener::currrent_coverage() {
        QMap<int, SourceInfo> sourcess;
        QMap<int, QMap<int, LineInfo> > coveragee;
        QMapIterator<int, SourceInfo*> iter(sources);
        while(iter.hasNext()) {
            iter.next();
            sourcess.insert(iter.key(),*iter.value());
        }
        QMapIterator<int,  QMap<int, LineInfo>*> iter2(coverage);
        while(iter2.hasNext()) {
            iter2.next();
            coveragee.insert(iter2.key(),*iter2.value());
        }

        return CodeCoverage(sourcess, coveragee);
    }



    void CoverageListener::new_code(intptr_t id, QString source, QUrl url, int startline) {
        if (is_omit(url))
            return;
        int hash = get_hash(url,startline);
        webkit_pointers.insert(id,hash);
        if (!sources.contains(hash)) {
            qDebug() << "Loaded new code: " << url << " at line " << QString::number(startline);
            SourceInfo* info_p = new SourceInfo(source, url, startline);
            sources.insert(hash, info_p);
            coverage.insert(hash, new QMap<int, LineInfo>());
        }
    }



    void CoverageListener::statement_executed(intptr_t sourceID, std::string function_name, int linenumber) {
        int hash = webkit_pointers[sourceID];
        QMap<int, LineInfo> *map = coverage.value(hash, 0);
        if (map == 0) {
            map = new QMap<int, LineInfo>();
        }
        coverage.insert(hash,map);
        if (map->contains(linenumber)) {
            LineInfo p = map->value(hash);
            p.line_executed();
            map->insert(linenumber, p);
        } else {
            LineInfo p;
            p.line_executed();
            map->insert(linenumber, p);
        }
    }
}
