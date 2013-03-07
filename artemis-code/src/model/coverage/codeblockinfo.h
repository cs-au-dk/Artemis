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

#ifndef CODEBLOCKINFO_H
#define CODEBLOCKINFO_H

#include <QString>
#include <QSet>
#include <QUrl>

namespace artemis {

typedef uint codeblockid_t;

class CodeBlockInfo
{

public:
    CodeBlockInfo(QString functionName, size_t bytecodeSize);

    size_t getBytecodeSize() const;
    void setBytecodeCovered(uint bytecodeOffset);
    size_t numCoveredBytecodes() const;

    static codeblockid_t getId(unsigned sourceOffset, const QUrl& url, int startline);

private:
    QString mFunctionName;
    size_t mBytecodeSize;
    QSet<uint> mCoveredBytecodes;

};

}

#endif // CODEBLOCKINFO_H
