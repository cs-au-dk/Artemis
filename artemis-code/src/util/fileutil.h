#ifndef FILEUTIL_H
#define FILEUTIL_H

#include <QString>
#include <QFile>

namespace artemis
{

void write_string_to_file(QString filename, QString data);
void create_dir(QString path, QString folder_name);
QString read_file(QFile& f);

}

#endif // FILEUTIL_H
