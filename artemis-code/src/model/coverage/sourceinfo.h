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
#ifndef SOURCEINFO_H
#define SOURCEINFO_H

#include <QObject>
#include <QUrl>
#include <QDebug>

namespace artemis
{

class SourceInfo : public QObject
{
    Q_OBJECT

public:
    SourceInfo(QObject* parent, const QString source, const QUrl url, const int startline);
    SourceInfo(QObject* parent, const SourceInfo* other);

    QString getSource() const;
    QString getURL() const;
    int getStartLine() const;

    QString toString() const;
    QDebug friend operator<<(QDebug dbg, const SourceInfo& e);

private:
    QString mSource;
    QUrl mUrl;
    int mStartLine;
};

}

#endif // SOURCEINFO_H
