#ifndef CODEBLOCKINFO_H
#define CODEBLOCKINFO_H

#include <QString>
#include <QSet>

namespace artemis {

class CodeBlockInfo
{

public:
    CodeBlockInfo(QString functionName, size_t bytecodeSize);

    size_t getBytecodeSize() const;

private:
    QString mFunctionName;
    size_t mBytecodeSize;

};

}

#endif // CODEBLOCKINFO_H
