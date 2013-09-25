/*
 * Copyright 2012 Aarhus University
 *
 * Licensed under the GNU General Public License, Version 3 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *          http://www.gnu.org/licenses/gpl-3.0.html
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#ifndef SOURCEINFO_H
#define SOURCEINFO_H

#include <inttypes.h>

#include <QDebug>
#include <QSharedPointer>

namespace artemis
{

typedef uint sourceid_t;

class SourceInfo
{

public:
    SourceInfo(const QString source, const QString url, const int startline);

    QString getSource() const;
    QString getURL() const;

    int getStartLine() const;

    void setLineCovered(uint lineNumber);
    void setLineSymbolicCovered(uint lineNumber);
    void setRangeCovered(int divot, int startOffset, int endOffset);
    void setRangeSymbolicCovered(int divot, int startOffset, int endOffset);
    QSet<uint> getLineCoverage() const;
    QSet<uint> getSymbolicLineCoverage() const;
    QMap<int,int> getRangeCoverage() const;
    QMap<int,int> getSymbolicRangeCoverage() const;

    QString toString() const;
    QDebug friend operator<<(QDebug dbg, const SourceInfo& e);

    static sourceid_t getId(const QString& sourceUrl, uint sourceStartLine);

private:
    QString mSource;
    QString mUrl;
    int mStartLine;
    QSet<uint> mCoverage;
    QSet<uint> mSymbolicCoverage;
    QMap<int, int> mSymbolicStartRangeCoverage;
    QMap<int,int> mSymbolicEndRangeCoverage;
    QMap<int,int> mStartRangeCoverage;
    QMap<int,int> mEndRangeCoverage;
};

typedef QSharedPointer<SourceInfo> SourceInfoPtr;
typedef QSharedPointer<const SourceInfo> SourceInfoConstPtr;

}

#endif // SOURCEINFO_H
