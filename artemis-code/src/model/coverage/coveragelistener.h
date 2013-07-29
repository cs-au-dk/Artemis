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
#include <QWebExecutionListener>
#include <QSource>

#include "runtime/input/baseinput.h"

#include "sourceinfo.h"
#include "codeblockinfo.h"

namespace artemis
{

const QString DONT_MEASURE_COVERAGE("http://this-is-fake-dont-do-coverage.fake");

class CoverageListener : public QObject
{
    Q_OBJECT

public:
    explicit CoverageListener(const QSet<QUrl>& ignoredUrls);

    QList<sourceid_t> getSourceIDs();
    SourceInfoPtr getSourceInfo(sourceid_t sourceID);

    size_t getNumCoveredLines();

    float getBytecodeCoverage(QSharedPointer<const BaseInput> inputEvent) const;

    void notifyStartingEvent(QSharedPointer<const BaseInput> inputEvent);
    void notifyStartingLoad();

    QString toString() const;

private:

    QSet<QUrl> mIgnoredUrls;

    // (inputHashCode -> set<codeBlockID>
    QMap<int, QSet<codeblockid_t>* > mInputToCodeBlockMap;
    int mInputBeingExecuted;

    // (sourceID -> SourceInfo)
    QMap<sourceid_t, SourceInfoPtr> mSources;

    // (codeBlockID -> CodeBlockInfo)
    QMap<codeblockid_t, QSharedPointer<CodeBlockInfo> > mCodeBlocks;


public slots:

    void slJavascriptScriptParsed(QString sourceCode, QSource* source);
    void slJavascriptFunctionCalled(QString functionName, size_t bytecodeSize, uint functionStartLine, uint sourceOffset, QSource* source);
    void slJavascriptBytecodeExecuted(ByteCodeInfoStruct* binfo, uint sourceOffset, QSource* source);
    void slJavascriptStatementExecuted(uint linenumber, QSource* source);

};

typedef QSharedPointer<CoverageListener> CoverageListenerPtr;

}

#endif // COVERAGELISTENER_H
