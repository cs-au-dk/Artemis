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

#include <assert.h>

#include "artemisglobals.h"
#include "util/urlutil.h"
#include "statistics/statsstorage.h"

#include "coveragelistener.h"

namespace artemis
{

CoverageListener::CoverageListener(QObject* parent) :
    QObject(parent),
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

void CoverageListener::newCode(intptr_t sourceTemporalID, QString source, QUrl url, int startline)
{
    if (isOmit(url)) {
        return;
    }

    if (!mSourceIdMap.contains(sourceTemporalID)) {
        int sourceID = qHash(url) * 53 + startline * 29;
        mSourceIdMap.insert(sourceTemporalID, sourceID);
    }

    int sourceID = mSourceIdMap.value(sourceTemporalID);

    if (!sources.contains(sourceID)) {
        qDebug() << "Loaded new code (id " << sourceID << "): " << url << " at line " << QString::number(startline);
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
    if (!mCodeBlockIdMap.contains(codeBlockTemporalID)) {
        codeblockid_t codeBlockID = qHash(functionName);
        mCodeBlockIdMap.insert(codeBlockTemporalID, codeBlockID);
    }

    codeblockid_t codeBlockID = mCodeBlockIdMap.value(codeBlockTemporalID);

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

    codeblockid_t codeBlockID = mCodeBlockIdMap.value(codeBlockTemporalID, -1);

    if (codeBlockID == -1) {
        return; // ignore unknown code block
    }

    mCoveredBytecodes.value(codeBlockID)->insert(bytecodeOffset);

}

void CoverageListener::notifyStartingEvent(QSharedPointer<const BaseInput> inputEvent)
{
    mInputBeingExecuted = inputEvent->hashCode();

    if (!mInputCodeBlockMap.contains(mInputBeingExecuted)) {
        mInputCodeBlockMap.insert(mInputBeingExecuted, new QSet<codeblockid_t>());
    }
}

float CoverageListener::getBytecodeCoverage(QSharedPointer<const BaseInput> inputEvent)
{
    mInputBeingExecuted = inputEvent->hashCode();

    if (!mInputCodeBlockMap.contains(mInputBeingExecuted)) {
        return 0;
    }

    size_t totalBytecodes = 0;
    size_t executedBytecodes = 0;

    foreach (codeblockid_t codeBlockID, mInputCodeBlockMap.value(mInputBeingExecuted)->toList()) {
        totalBytecodes += mCodeBlocks.value(codeBlockID)->getBytecodeSize();
        executedBytecodes += mCoveredBytecodes.value(codeBlockID)->size();
    }

    return float(executedBytecodes) / float(totalBytecodes);

}


}
