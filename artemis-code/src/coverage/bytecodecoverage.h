#ifndef BYTECODECOVERAGE_H
#define BYTECODECOVERAGE_H

#include <Qt>
#include <QtDebug>

namespace artemis {

class ByteCodeCoverage
{
public:
    ByteCodeCoverage(uint lineno = 0, uint opcode = 0);


    QDebug friend operator<<(QDebug dbg, const ByteCodeCoverage &e);

    void bytecode_executed();
    uint hit_count();
    uint line_number();
    uint opcodeID();

private:
    // How times have this bytecode been hit so far;
    uint m_hit_count;
    // Line number in source where this bytecode is matched
    uint m_line_no;
    //Type
    uint m_opcode;

};

}

#endif // BYTECODECOVERAGE_H
