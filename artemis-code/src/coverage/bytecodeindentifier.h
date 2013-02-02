#ifndef BYTECODEINDENTIFIER_H
#define BYTECODEINDENTIFIER_H

#include <QUrl>
#include <QDebug>

namespace artemis
{

class ByteCodeIndentifier
{
public:
    ByteCodeIndentifier(QUrl url, int offset);

    QUrl url();
    int offset();

    bool operator==(const ByteCodeIndentifier& other) const;
    QDebug friend operator<<(QDebug dbg, const ByteCodeIndentifier& e);
    uint hashcode() const;

private:
    QUrl m_url;
    int m_offset;
};

}

inline uint qHash(const artemis::ByteCodeIndentifier& d)
{
    return d.hashcode();
}

#endif // BYTECODEINDENTIFIER_H
