#include "sourceidentifier.h"

namespace artemis
{

SourceIdentifier::SourceIdentifier(QUrl& url, int source_offset)
{
    this->m_url = url;
    this->m_source_offset = source_offset;
}

bool SourceIdentifier::operator==(const SourceIdentifier& other) const
{
    return
        this->m_source_offset == other.m_source_offset &&
        this->m_url == other.m_url;
}

QDebug operator<<(QDebug dbg, const SourceIdentifier& e)
{
    dbg.nospace() << "SourceIdentifier[url: " << e.m_url << ", source_offset: " << e.m_source_offset << "]";
    return dbg.space();
}

uint SourceIdentifier::hashcode() const
{
    return this->m_source_offset * 17 + qHash(this->m_url) * 101;
}

}
