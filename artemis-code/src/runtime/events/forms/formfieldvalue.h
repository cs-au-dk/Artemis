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
#ifndef FORMFIELDVALUE_H
#define FORMFIELDVALUE_H

#include <QObject>
#include <QString>

namespace artemis
{

class FormFieldValue : public QObject
{
    Q_OBJECT

public:
    FormFieldValue(QObject* parent, QString value);
    FormFieldValue(QObject* parent, bool value);
    FormFieldValue(QObject* parent);

    bool getBool() const;
    QString getStr() const;
    bool isNoValue() const;
    QString stringRepresentation() const;

    QDebug friend operator<<(QDebug dbg, const FormFieldValue& f);

private:
    QString strVal;
    bool boolVal;
    bool isBool;
    bool isNoVal;
};

}

#endif // FORMFIELDVALUE_H
