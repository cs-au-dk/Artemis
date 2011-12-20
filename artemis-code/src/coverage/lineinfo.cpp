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
#include "lineinfo.h"

namespace artemis {

    LineInfo::LineInfo()
    {
        m_hitcount = 0;
    }

    LineInfo::LineInfo(const LineInfo &other) {
        m_hitcount = other.m_hitcount;
    }

    bool LineInfo::is_executed() const {
        return m_hitcount > 0;
    }

    int LineInfo::hit_count() const {
        return m_hitcount;
    }

    void LineInfo::line_executed() {
        m_hitcount++;
    }

    uint LineInfo::hashcode() const {
        return 17*m_hitcount;
    }

    LineInfo& LineInfo::operator=(const LineInfo &other) {
        m_hitcount = other.m_hitcount;
        return *this;
    }

    bool LineInfo::operator==(const LineInfo& other) const {
        return m_hitcount == other.m_hitcount;
    }

    QDebug operator<<(QDebug dbg, const LineInfo &e) {
        dbg.nospace() << (e.m_hitcount > 0 ? "COVERED[" + QString::number(e.m_hitcount) + QString(']') : "UNCOVERED");
        return dbg.space();
    }
}



