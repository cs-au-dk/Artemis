#include "fileutil.h"
#include <QFile>
#include <QDir>
#include <QTextStream>

namespace artemis
{

void writeStringToFile(QString filename, QString data)
{
    QFile file(filename);
    file.open(QIODevice::WriteOnly | QIODevice::Text);
    QTextStream out(&file);
    out << (data.isEmpty() ? " " : data);
    file.close();
    out.flush();
}

void createDir(QString path, QString folderName)
{
    if (QDir().exists(path + "/" + folderName))
        { return; }

    QDir().mkdir(path + "/" + folderName);
}

QString readFile(QString fileS)
{
    QFile f(fileS);
    f.open(QFile::ReadOnly | QFile::Text);
    QTextStream in(&f);
    return in.readAll();
}

}
