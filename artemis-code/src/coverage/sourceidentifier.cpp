#include "sourceidentifier.h"

namespace artemis
{

SourceIdentifier::SourceIdentifier(QUrl& url, int sourceOffset)
{
    this->mUrl = url;
    this->mSourceOffset = sourceOffset;
}

bool SourceIdentifier::operator==(const SourceIdentifier& other) const
{
    return
        this->mSourceOffset == other.mSourceOffset &&
        this->mUrl == other.mUrl;
}

QDebug operator<<(QDebug dbg, const SourceIdentifier& e)
{
    dbg.nospace() << "SourceIdentifier[url: " << e.mUrl << ", sourceOffset: " << e.mSourceOffset << "]";
    return dbg.space();
}

uint SourceIdentifier::hashcode() const
{
    return this->mSourceOffset * 17 + qHash(this->mUrl) * 101;
}

}
