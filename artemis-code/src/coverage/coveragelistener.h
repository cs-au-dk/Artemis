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
#ifndef COVERAGELISTENER_H
#define COVERAGELISTENER_H

#include <inttypes.h>

#include <QObject>
#include <QUrl>
#include <QMap>
#include <QSet>
#include <QSharedPointer>

#include "runtime/input/baseinput.h"

#include "sourceinfo.h"
#include "codeblockinfo.h"

namespace artemis
{

typedef int codeblockid_t;

class CoverageListener : public QObject
{
    Q_OBJECT

public:
    explicit CoverageListener();

    QList<int> getSourceIDs();
    SourceInfo* getSourceInfo(int sourceID);
    QSet<int> getLineCoverage(int sourceID);

    size_t getNumCoveredLines();

    float getBytecodeCoverage(QSharedPointer<const BaseInput> inputEvent) const;

    void notifyStartingEvent(QSharedPointer<const BaseInput> inputEvent);
    void notifyStartingLoad();

    QString toString() const;

private:

    // (sourceTemporalID -> sourceID) needed as the sourceTemporalID changes for each new page-execution
    QMap<intptr_t, int> mSourceIdMap;

    // (sourceID -> SourceInfo)
    QMap<int, SourceInfo*> sources;

    // (sourceID -> set<lines>)
    QMap<int, QSet<int>* > coverage;

    // (codeBlockTemporalID -> codeBlockID) needed as the codeBlockTemporalID changes for each new page-execution
    QMap<intptr_t, codeblockid_t> mCodeBlockIdMap;

    // (inputHashCode -> set<codeBlockID>
    QMap<int, QSet<codeblockid_t>* > mInputCodeBlockMap;
    int mInputBeingExecuted;

    // (codeBlockID -> CodeBlockInfo)
    QMap<codeblockid_t, QSharedPointer<CodeBlockInfo> > mCodeBlocks;

    // (codeBlockID -> set<bytecode offsets>
    QMap<codeblockid_t, QSet<int>* > mCoveredBytecodes;


public slots:

    void newCode(intptr_t sourceTemporalID, QString source, QUrl url, int startline);
    void statementExecuted(intptr_t sourceTemporalID, int linenumber);

    void slJavascriptFunctionCalled(intptr_t codeBlockTemporalID, QString functionName, size_t bytecodeSize);
    void slJavascriptBytecodeExecuted(intptr_t codeBlockTemporalID, size_t bytecodeOffset);

};

typedef QSharedPointer<CoverageListener> CoverageListenerPtr;

}

#endif // COVERAGELISTENER_H
