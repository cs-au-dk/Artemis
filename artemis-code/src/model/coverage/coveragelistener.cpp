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

#include <assert.h>
#include <QDebug>
#include <QWebExecutionListener>
#include "artemisglobals.h"
#include "util/urlutil.h"
#include "statistics/statsstorage.h"

#include "coveragelistener.h"

#include "util/loggingutil.h"
namespace artemis
{

CoverageListener::CoverageListener(const QSet<QUrl>& ignoredUrls) :
    QObject(NULL),
    mIgnoredUrls(ignoredUrls),
    mInputBeingExecuted(-1)
{
    mIgnoredUrls.insert(DONT_MEASURE_COVERAGE);
}

QList<sourceid_t> CoverageListener::getSourceIDs()
{
    return mSources.keys();
}

SourceInfoPtr CoverageListener::getSourceInfo(sourceid_t sourceID)
{
    return mSources.value(sourceID);
}

size_t CoverageListener::getNumCoveredLines()
{
    size_t coveredLines = 0;

    foreach(SourceInfoPtr source, mSources.values()) {
        coveredLines += source->getLineCoverage().size();
    }

    return coveredLines;
}

float CoverageListener::getBytecodeCoverage(QSharedPointer<const BaseInput> inputEvent) const
{

    uint hashcode = inputEvent->hashCode();

    if (!mInputToCodeBlockMap.contains(hashcode)) {
        return 0;
    }

    size_t totalBytecodes = 0;
    size_t executedBytecodes = 0;

    foreach (codeblockid_t codeBlockID, mInputToCodeBlockMap.value(hashcode)->toList()) {
        QSharedPointer<CodeBlockInfo> codeBlockInfo =  mCodeBlocks.value(codeBlockID);
        totalBytecodes += codeBlockInfo->getBytecodeSize();
        executedBytecodes += codeBlockInfo->numCoveredBytecodes();
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
    if (!mInputToCodeBlockMap.contains(mInputBeingExecuted)) {
        mInputToCodeBlockMap.insert(mInputBeingExecuted, new QSet<codeblockid_t>());
    }
}

void CoverageListener::notifyStartingLoad()
{
    mInputBeingExecuted = -1;
}

void CoverageListener::slJavascriptScriptParsed(QString sourceCode, QSource* source)
{   

    if(mIgnoredUrls.contains(source->getUrl())){
        return;
    }

    sourceid_t sourceID = SourceInfo::getId(source->getUrl(), source->getStartLine());

    if (!mSources.contains(sourceID)) {

        qDebug() << "Loaded script: " << source->getUrl() << " (line " << QString::number(source->getStartLine()) << ")";

        SourceInfoPtr sourceInfo = SourceInfoPtr(new SourceInfo(sourceCode, source->getUrl(), source->getStartLine()));
        mSources.insert(sourceID, sourceInfo);
    }
}

void CoverageListener::slJavascriptStatementExecuted(uint linenumber, QSource* source)
{

    statistics()->accumulate("WebKit::coverage::covered", 1);

    sourceid_t sourceID = SourceInfo::getId(source->getUrl(), source->getStartLine());
    SourceInfoPtr sourceInfo = mSources.value(sourceID, SourceInfoPtr(NULL));

    if (sourceInfo.isNull()) {
        qDebug() << "Warning, unknown line " << linenumber << " executed in file at " << source->getUrl() << " offset " << source->getStartLine();
        return;
    }

//    sourceInfo->setLineCovered(linenumber);
}

void CoverageListener::slJavascriptFunctionCalled(QString functionName, size_t bytecodeSize, uint functionStartLine, uint sourceOffset, QSource* source)
{

    codeblockid_t codeBlockID = CodeBlockInfo::getId(sourceOffset, source->getUrl(), source->getStartLine());

    if (!mCodeBlocks.contains(codeBlockID)) {
        mCodeBlocks.insert(codeBlockID, QSharedPointer<CodeBlockInfo>(new CodeBlockInfo(functionName, bytecodeSize)));
    }

    if (mInputBeingExecuted != -1) {
        mInputToCodeBlockMap.value(mInputBeingExecuted)->insert(codeBlockID);
    }

}

void CoverageListener::slJavascriptBytecodeExecuted(const ByteCodeInfoStruct& binfo, uint sourceOffset, QSource* source)
{

    codeblockid_t codeBlockID = CodeBlockInfo::getId(sourceOffset, source->getUrl(), source->getStartLine());
    QSharedPointer<CodeBlockInfo> codeBlockInfo = mCodeBlocks.value(codeBlockID, QSharedPointer<CodeBlockInfo>(NULL));

    if (!codeBlockInfo.isNull()) {
        codeBlockInfo->setBytecodeCovered(binfo.bytecodeOffset);
    }

    sourceid_t sourceID = SourceInfo::getId(source->getUrl(), source->getStartLine());
    SourceInfoPtr sourceInfo = mSources.value(sourceID, SourceInfoPtr(NULL));

    if (!sourceInfo.isNull()) {
        if(binfo.isSymbolic){
            sourceInfo->setRangeSymbolicCovered(binfo.divot,binfo.startOffset,binfo.endOffset);
            sourceInfo->setLineSymbolicCovered(binfo.linenumber);
        } else {
            sourceInfo->setRangeCovered(binfo.divot,binfo.startOffset,binfo.endOffset);
            sourceInfo->setLineCovered(binfo.linenumber);
        }
    }

}

QString CoverageListener::toString() const
{
    QString output;

    foreach (int inputHash, mInputToCodeBlockMap.keys()) {
        output += "Input(" + QString::number(inputHash) + ")\n";

        foreach (codeblockid_t codeBlockID, mInputToCodeBlockMap.value(inputHash)->toList()) {
            output += "  CodeBlockID (" + QString::number(codeBlockID) + ") size = " + QString::number(mCodeBlocks.value(codeBlockID)->getBytecodeSize()) + "\n";
        }
    }

    return output;

}


}
