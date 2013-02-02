#ifndef SOURCEIDENTIFIER_H
#define SOURCEIDENTIFIER_H

#include <QDebug>
#include <QUrl>

namespace artemis
{

class SourceIdentifier
{
public:
    SourceIdentifier(QUrl& url, int sourceOffset);

    bool operator==(const SourceIdentifier& other) const;
    QDebug friend operator<<(QDebug dbg, const SourceIdentifier& e);
    uint hashcode() const;

private:
    QUrl mUrl;
    int mSourceOffset;
};

}

inline uint qHash(const artemis::SourceIdentifier& d)
{
    return d.hashcode();
}

#endif // SOURCEIDENTIFIER_H
