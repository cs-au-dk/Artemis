/*
 * Copyright 2012 Aarhus University
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
#include "sourceinfo.h"

namespace artemis
{

SourceInfo::SourceInfo(const QString source, const QUrl url, const int startline) :
    mSource(source),
    mUrl(url),
    mStartLine(startline)
{
}

QString SourceInfo::getSource() const
{
    return mSource;
}

int SourceInfo::getStartLine() const
{
    return mStartLine;
}

QString SourceInfo::getURL() const
{
    return mUrl.toString();
}

void SourceInfo::setLineCovered(uint lineNumber)
{
    mCoverage.insert(lineNumber);
}

QSet<uint> SourceInfo::getLineCoverage() const
{
    return mCoverage;
}

QString SourceInfo::toString() const
{
    return "[" + mUrl.toString() + ", " + QString::number(mStartLine) + ", " + mSource + "ENDOFJSOURCE]";
}

QDebug operator<<(QDebug dbg, const SourceInfo& e)
{
    dbg.nospace() << e.mUrl << "[" << QString::number(e.mStartLine) << "]";
    return dbg.space();
}

sourceid_t SourceInfo::getId(const QUrl& sourceUrl, uint sourceStartLine)
{
    return qHash(sourceUrl) * 53 + sourceStartLine * 29;
}

}
