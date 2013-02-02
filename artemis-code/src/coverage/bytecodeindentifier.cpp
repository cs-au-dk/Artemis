#include "bytecodeindentifier.h"

namespace artemis
{

ByteCodeIndentifier::ByteCodeIndentifier(QUrl url, int offset)
{
    this->mUrl = url;
    this->mOffset = offset;
}

QUrl ByteCodeIndentifier::url()
{
    return this->mUrl;
}

int ByteCodeIndentifier::offset()
{
    return this->mOffset;
}

bool ByteCodeIndentifier::operator==(const ByteCodeIndentifier& other) const
{
    return this->mOffset == other.mOffset && this->mUrl == other.mUrl;
}

QDebug operator<<(QDebug dbg, const ByteCodeIndentifier& e)
{
    dbg.nospace() << "ByteCodeIdentifier[url: " << e.mOffset << ", offset: " << e.mOffset << "]";
    return dbg.space();
}

uint ByteCodeIndentifier::hashcode() const
{
    return qHash(mUrl) * 7 + 11 * mOffset;
}


}
