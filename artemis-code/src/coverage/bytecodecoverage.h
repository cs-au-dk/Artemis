#ifndef BYTECODECOVERAGE_H
#define BYTECODECOVERAGE_H

#include <Qt>
#include <QtDebug>

namespace artemis
{

class ByteCodeCoverage
{
public:
    ByteCodeCoverage(uint lineno = 0, uint opcode = 0);


    QDebug friend operator<<(QDebug dbg, const ByteCodeCoverage& e);

    void bytecodeExecuted();
    uint hitCount();
    uint lineNumber();
    uint opcodeID();

private:
    // How times have this bytecode been hit so far;
    uint mHitCount;
    // Line number in source where this bytecode is matched
    uint mLineNo;
    //Type
    uint mOpcode;

};

}

#endif // BYTECODECOVERAGE_H
