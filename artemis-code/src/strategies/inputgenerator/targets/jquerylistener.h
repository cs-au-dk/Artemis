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

#include <QObject>
#include <QList>

#ifndef JQUERYLISTENER_H
#define JQUERYLISTENER_H

namespace artemis
{

typedef struct jqueryEventT {
    QString elementSignature;
    QString event;
    QString selector;
} jqueryEvent;

class JQueryListener : public QObject
{
    Q_OBJECT

public:
    explicit JQueryListener(QObject* parent);
    void reset();
    QList<QString> lookup(QString elementSignature, QString event);

protected:
    QList<jqueryEvent*> jqueryEvents;

public slots:
    void slEventAdded(QString elementSignature, QString event, QString selector);
};

}

#endif
