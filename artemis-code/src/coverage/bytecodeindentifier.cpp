#include "bytecodeindentifier.h"

namespace artemis {

ByteCodeIndentifier::ByteCodeIndentifier(QUrl url, int offset)
{
    this->m_url = url;
    this->m_offset = offset;
}

QUrl ByteCodeIndentifier::url() {
    return this->m_url;
}

int ByteCodeIndentifier::offset() {
    return this->m_offset;
}

bool ByteCodeIndentifier::operator==(const ByteCodeIndentifier& other) const {
    return this->m_offset == other.m_offset && this->m_url == other.m_url;
}

QDebug operator<<(QDebug dbg, const ByteCodeIndentifier &e) {
    dbg.nospace() << "ByteCodeIdentifier[url: " << e.m_offset << ", offset: " << e.m_offset << "]";
    return dbg.space();
}

uint ByteCodeIndentifier::hashcode() const {
    return qHash(m_url)*7 + 11*m_offset;
}


}
