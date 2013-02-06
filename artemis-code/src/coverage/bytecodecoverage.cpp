#include "bytecodecoverage.h"

namespace artemis
{

ByteCodeCoverage::ByteCodeCoverage(uint lineno, uint opcode)
{
    this->mLineNo = lineno;
    this->mOpcode = opcode;
    this->mHitCount = 0;
}

QDebug operator<<(QDebug dbg, const ByteCodeCoverage& e)
{
    dbg.nospace() << "ByteCodeCoverage [opcode="
                  << e.mOpcode
                  << ", hitCount="
                  << e.mHitCount
                  << ", lineNo="
                  << e.mLineNo << "]";
    return dbg.space();
}

void ByteCodeCoverage::bytecodeExecuted()
{
    this->mHitCount++;
}

uint ByteCodeCoverage::hitCount()
{
    return this->mHitCount;
}

uint ByteCodeCoverage::lineNumber()
{
    this->mLineNo;
}

uint ByteCodeCoverage::opcodeID()
{
    return this->mOpcode;
}

}
