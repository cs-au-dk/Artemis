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

#include "codeblockinfo.h"

namespace artemis {

CodeBlockInfo::CodeBlockInfo(QString functionName, size_t bytecodeSize) :
    mFunctionName(functionName),
    mBytecodeSize(bytecodeSize)
{
}

size_t CodeBlockInfo::getBytecodeSize() const
{
    return mBytecodeSize;
}

size_t CodeBlockInfo::numCoveredBytecodes() const
{
    return mCoveredBytecodes.size();
}

codeblockid_t CodeBlockInfo::getId(unsigned int sourceOffset, const QUrl& url, int startline)
{
    return sourceOffset * 7 + qHash(url) + 37 * startline;
}

void CodeBlockInfo::setBytecodeCovered(uint bytecodeOffset)
{
    mCoveredBytecodes.insert(bytecodeOffset);
}

}
