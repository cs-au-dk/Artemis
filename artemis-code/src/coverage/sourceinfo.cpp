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

namespace artemis
{

SourceInfo::SourceInfo(QObject* parent, const QString source, const QUrl url, const int startline) : QObject(parent)
{
    this->mSource = source;
    this->mUrl = url;
    this->mStartLine = startline;
}

SourceInfo::SourceInfo(QObject* parent, const SourceInfo* other) : QObject(parent)
{
    this->mSource = other->mSource;
    this->mUrl = other->mUrl;
    this->mStartLine = other->mStartLine;
}

QString SourceInfo::source() const
{
    return this->mSource;
}

QUrl SourceInfo::url() const
{
    return this->mUrl;
}

int SourceInfo::startLine() const
{
    return this->mStartLine;
}

QDebug operator<<(QDebug dbg, const SourceInfo& e)
{
    dbg.nospace() << e.mUrl << "[" << QString::number(e.mStartLine) << "]";
    return dbg.space();
}

QString SourceInfo::getSource() const
{
    return QString(mSource);
}

int SourceInfo::getStartLine() const
{
    return mStartLine;
}

QString SourceInfo::getURL() const
{
    return mUrl.toString();
}

QString SourceInfo::toString() const
{
    return "[" + mUrl.toString() + ", " + QString::number(mStartLine) + ", " + mSource + "ENDOFJSOURCE]";
}

}
