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

}
