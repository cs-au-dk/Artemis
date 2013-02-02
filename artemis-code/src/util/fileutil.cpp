#include "fileutil.h"
#include <QFile>
#include <QDir>
#include <QTextStream>

namespace artemis
{

void write_string_to_file(QString filename, QString data)
{
    QFile file(filename);
    file.open(QIODevice::WriteOnly | QIODevice::Text);
    QTextStream out(&file);
    out << (data.isEmpty() ? " " : data);
    file.close();
    out.flush();
}

void create_dir(QString path, QString folder_name)
{
    if (QDir().exists(path + "/" + folder_name))
        { return; }

    QDir().mkdir(path + "/" + folder_name);
}

QString read_file(QString file_s)
{
    QFile f(file_s);
    f.open(QFile::ReadOnly | QFile::Text);
    QTextStream in(&f);
    return in.readAll();
}

}
