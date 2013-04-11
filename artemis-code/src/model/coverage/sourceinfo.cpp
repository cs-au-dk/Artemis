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
#include <QDebug>

namespace artemis
{

SourceInfo::SourceInfo(const QString source, const QString url, const int startline) :
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
    return mUrl;
}

void SourceInfo::setLineCovered(uint lineNumber)
{
    mCoverage.insert(lineNumber);
}

void SourceInfo::setLineSymbolicCovered(uint lineNumber){
    mSymbolicCoverage.insert(lineNumber);
}

void SourceInfo::setRangeCovered(int divot, int startOffset, int endOffset){
    mStartRangeCoverage[divot] = std::max(startOffset,mStartRangeCoverage[divot]);
    mEndRangeCoverage[divot] = std::max(endOffset,mEndRangeCoverage[divot]);
}

void SourceInfo::setRangeSymbolicCovered(int divot, int startOffset, int endOffset){
    mSymbolicStartRangeCoverage[divot] = std::max(startOffset,mSymbolicStartRangeCoverage[divot]);
    mSymbolicEndRangeCoverage[divot] = std::max(endOffset,mSymbolicEndRangeCoverage[divot]);
}


QSet<uint> SourceInfo::getLineCoverage() const
{
    return mCoverage;
}

QSet<uint> SourceInfo::getSymbolicLineCoverage() const
{
    return mSymbolicCoverage;
}

QMap<int,int> SourceInfo::getRangeCoverage() const
{
    QMap<int,int> returnMap;
    int lastEnd = 0,lastStart = 0;
    foreach(int key, mStartRangeCoverage.keys()){
        int end = key+mEndRangeCoverage[key],
                start = key-mStartRangeCoverage[key];
        if(start < end){

            if(start <= lastEnd){
                returnMap[lastStart] = end;
            } else {
                returnMap[start] = end;
            }
        }

        lastEnd = end;
        lastStart = start;
    }

    return returnMap;
}

QMap<int,int> SourceInfo::getSymbolicRangeCoverage() const
{
    QMap<int,int> returnMap;
    int lastEnd = 0,lastStart = 0;
    foreach(int key, mSymbolicStartRangeCoverage.keys()){
        int end = key+mSymbolicEndRangeCoverage[key],
                start = key-mSymbolicStartRangeCoverage[key];
        if(start < end){

        if(start <= lastEnd){
            returnMap[lastStart] = end;
        } else {
            returnMap[start] = end;
        }
        }
        lastEnd = end;
        lastStart = start;
    }

    return returnMap;
}



QString SourceInfo::toString() const
{
    return "[" + mUrl + ", " + QString::number(mStartLine) + ", " + mSource + "ENDOFJSOURCE]";
}

QDebug operator<<(QDebug dbg, const SourceInfo& e)
{
    dbg.nospace() << e.mUrl << "[" << QString::number(e.mStartLine) << "]";
    return dbg.space();
}

sourceid_t SourceInfo::getId(const QString& sourceUrl, uint sourceStartLine)
{
    return qHash(sourceUrl) * 53 + sourceStartLine * 29;
}

}
