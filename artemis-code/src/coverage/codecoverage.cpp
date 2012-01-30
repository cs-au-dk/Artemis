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
#include "codecoverage.h"
#include "artemisglobals.h"

namespace artemis {

    CodeCoverage::CodeCoverage(const QMap<int, SourceInfo> &sources, const QMap<int, QMap<int, LineInfo> > &coverage)
    {
        m_sources.clear();
        m_coverage.clear();
        m_sources = sources;
        m_coverage = coverage;
    }

    bool CodeCoverage::operator==(const CodeCoverage& other) const {
        return m_sources == other.m_sources && m_coverage == other.m_coverage;
    }

    QDebug operator<<(QDebug dbg, const CodeCoverage &e) {
        dbg.nospace() << e.m_coverage << "   " << e.m_sources;
        return dbg.space();
    }

    uint CodeCoverage::hashcode() const {
        return qHash(m_sources)*17 + qHash(m_coverage)*23;
    }

    QSet<int> CodeCoverage::source_ids() const {
        QSet<int> res;
        foreach (int p, m_sources.keys()) {
            res.insert(p);
        }
        return res;
    }

    const SourceInfo CodeCoverage::source_info(int id) const {
        Q_ASSERT(m_sources.contains(id));
        SourceInfo res = m_sources[id];
        return res;
    }

    QMap<int, LineInfo> CodeCoverage::line_info(int id) const {
        Q_ASSERT(m_coverage.contains(id));
        return m_coverage[id];
    }

}
