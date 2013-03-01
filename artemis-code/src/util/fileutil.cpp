/*
 * Copyright 2012 Aarhus University
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
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
