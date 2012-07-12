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
#include "sourceinfo.h"

namespace artemis {

    SourceInfo::SourceInfo(const QString source, const QUrl url, const int startline)
    {
        this->m_source = source;
        this->m_url = url;
        this->m_start_line = startline;
    }

    SourceInfo::SourceInfo(const SourceInfo &other) {
        this->m_source = other.m_source;
        this->m_url = other.m_url;
        this->m_start_line = other.m_start_line;
    }

    QString SourceInfo::source() const {
        return this->m_source;
    }

    QUrl SourceInfo::url() const{
        return this->m_url;
    }

    int SourceInfo::start_line() const {
        return this->m_start_line;
    }

    QDebug operator<<(QDebug dbg, const SourceInfo &e) {
        dbg.nospace() << e.m_url << "[" << QString::number(e.m_start_line) << "]";
        return dbg.space();
    }

    bool SourceInfo::operator==(const SourceInfo& other) const {
        return other.m_url == this->m_url && m_start_line == other.m_start_line;
    }

    SourceInfo::SourceInfo() {
        Q_ASSERT(false);
    }

    QString SourceInfo::getSource() const {
        return QString(m_source);
    }

    int SourceInfo::getStartLine() const {
        return m_start_line;
    }

    QString SourceInfo::getURL() const {
        return m_url.toString();
    }

    QString SourceInfo::toString() const {
        return "[" + m_url.toString() + ", " + QString::number(m_start_line) + ", " + m_source + "ENDOFJSOURCE]";
    }

}
