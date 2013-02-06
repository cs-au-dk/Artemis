#ifndef FILEUTIL_H
#define FILEUTIL_H

#include <QString>
#include <QFile>

namespace artemis
{

void writeStringToFile(QString filename, QString data);
void createDir(QString path, QString folderName);
QString readFile(QFile& f);

}

#endif // FILEUTIL_H
