#include "bytecodecoverage.h"

namespace artemis {

ByteCodeCoverage::ByteCodeCoverage(uint lineno, uint opcode)
{
    this->m_line_no = lineno;
    this->m_opcode = opcode;
    this->m_hit_count = 0;
}

QDebug operator<<(QDebug dbg, const ByteCodeCoverage &e) {
    dbg.nospace() << "ByteCodeCoverage [opcode="
                  << e.m_opcode
                  << ", hit_count="
                  << e.m_hit_count
                  << ", line_no="
                  << e.m_line_no << "]";
    return dbg.space();
}

void ByteCodeCoverage::bytecode_executed() {
    this->m_hit_count++;
}

uint ByteCodeCoverage::hit_count() {
    return this->m_hit_count;
}

uint ByteCodeCoverage::line_number() {
    this->m_line_no;
}

uint ByteCodeCoverage::opcodeID() {
    return this->m_opcode;
}

}
