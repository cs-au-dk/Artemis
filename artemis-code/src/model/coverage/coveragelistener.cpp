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

#include <assert.h>

#include "artemisglobals.h"
#include "util/urlutil.h"
#include "statistics/statsstorage.h"

#include "coveragelistener.h"

#include "util/loggingutil.h"
namespace artemis
{

CoverageListener::CoverageListener() :
    QObject(NULL),
    mInputBeingExecuted(-1)
{
}

QList<int> CoverageListener::getSourceIDs()
{
    return sources.keys();
}

SourceInfo* CoverageListener::getSourceInfo(int sourceID)
{
    return sources.value(sourceID);
}

QSet<int> CoverageListener::getLineCoverage(int sourceID)
{
    return *coverage.value(sourceID);
}

size_t CoverageListener::getNumCoveredLines()
{
    size_t coveredLines = 0;

    foreach(QSet<int>* codeCoverage, coverage.values()) {
        coveredLines += codeCoverage->size();
    }

    return coveredLines;
}

float CoverageListener::getBytecodeCoverage(QSharedPointer<const BaseInput> inputEvent) const
{
    uint hashcode = inputEvent->hashCode();

    if (!mInputCodeBlockMap.contains(hashcode)) {
        return 0;
    }

    size_t totalBytecodes = 0;
    size_t executedBytecodes = 0;

    foreach (codeblockid_t codeBlockID, mInputCodeBlockMap.value(hashcode)->toList()) {
        totalBytecodes += mCodeBlocks.value(codeBlockID)->getBytecodeSize();
        executedBytecodes += mCoveredBytecodes.value(codeBlockID)->size();

    }

    float coverage = 0;

    if (totalBytecodes > 0) {
        coverage = float(executedBytecodes) / float(totalBytecodes);
    }
    assert(coverage <= 1 && coverage >= 0);

    return coverage;

}

void CoverageListener::notifyStartingEvent(QSharedPointer<const BaseInput> inputEvent)
{
    mInputBeingExecuted = inputEvent->hashCode();
    if (!mInputCodeBlockMap.contains(mInputBeingExecuted)) {
        mInputCodeBlockMap.insert(mInputBeingExecuted, new QSet<codeblockid_t>());
    }
}

void CoverageListener::notifyStartingLoad()
{
    mInputBeingExecuted = -1;
}

void CoverageListener::newCode(intptr_t sourceTemporalID, QString source, QUrl url, int startline)
{   
    if (url == DONT_MEASURE_COVERAGE) {
        return;
    }

    if (!mSourceIdMap.contains(sourceTemporalID)) {
        int sourceID = qHash(url) * 53 + startline * 29;
        mSourceIdMap.insert(sourceTemporalID, sourceID);
    }

    int sourceID = mSourceIdMap.value(sourceTemporalID);

    if (!sources.contains(sourceID)) {

        qDebug() << "Loaded script: " << url.toString() << " (line " << QString::number(startline) << ")";

        SourceInfo* infoP = new SourceInfo(this, source, url, startline);
        sources.insert(sourceID, infoP);
        coverage.insert(sourceID, new QSet<int>());
    }
}

void CoverageListener::statementExecuted(intptr_t sourceTemporalID, int linenumber)
{

    int sourceID = mSourceIdMap.value(sourceTemporalID, -1);

    if (sourceID == -1) {
        qDebug() << "Warning, unknown line " << linenumber << " executed in file " << sourceTemporalID << " (temporal id)";
        return;
    }

    statistics()->accumulate("WebKit::coverage::covered", 1);

    QSet<int>* coveredLines = coverage.value(sourceID, NULL);
    assert(coveredLines != NULL);

    coveredLines->insert(linenumber);
}

void CoverageListener::slJavascriptFunctionCalled(intptr_t codeBlockTemporalID, QString functionName, size_t bytecodeSize)
{
    codeblockid_t codeBlockID = qHash(functionName+bytecodeSize);
    QList<codeblockid_t>* l;
    if (!mCodeBlockIdMap.contains(codeBlockTemporalID)) {
        l = new QList<codeblockid_t>();
        l->append(codeBlockID);
        mCodeBlockIdMap.insert(codeBlockTemporalID,l);

    } else {
        if(!((l = mCodeBlockIdMap.value(codeBlockTemporalID))->contains(codeBlockID))){
            l->removeOne(codeBlockID);
        }
        l->append(codeBlockID);
    }


    if (!mCodeBlocks.contains(codeBlockID)) {
        mCodeBlocks.insert(codeBlockID, QSharedPointer<CodeBlockInfo>(new CodeBlockInfo(functionName, bytecodeSize)));
        mCoveredBytecodes.insert(codeBlockID, new QSet<int>());
    }


    if (mInputBeingExecuted != -1) {
        mInputCodeBlockMap.value(mInputBeingExecuted)->insert(codeBlockID);
    }
}

void CoverageListener::slJavascriptBytecodeExecuted(intptr_t codeBlockTemporalID, size_t bytecodeOffset)
{
    QList<codeblockid_t>* codeBlockIDList = mCodeBlockIdMap.value(codeBlockTemporalID, NULL);

    if (codeBlockIDList == NULL) {
        return; // ignore unknown code block
    }
    mCoveredBytecodes.value(codeBlockIDList->last())->insert(bytecodeOffset);
}

QString CoverageListener::toString() const
{
    QString output;

    foreach (int inputHash, mInputCodeBlockMap.keys()) {
        output += "Input(" + QString::number(inputHash) + ")\n";

        foreach (codeblockid_t codeBlockID, mInputCodeBlockMap.value(inputHash)->toList()) {
            output += "  CodeBlockID (" + QString::number(codeBlockID) + ") size = " + QString::number(mCodeBlocks.value(codeBlockID)->getBytecodeSize()) + "\n";
        }
    }

    return output;

}


}
