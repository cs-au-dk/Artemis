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
#ifndef ARTEMISAPPLICATION_H
#define ARTEMISAPPLICATION_H

#include <QObject>
#include <QApplication>

#include "runtime/options.h"
#include "strategies/inputgenerator/inputgeneratorstrategy.h"
#include "runtime/runtime.h"

namespace artemis
{

class ArtemisApplication : public QObject
{
    Q_OBJECT
public:
    // TODO remove url from constructor
    ArtemisApplication(QObject* parent, QCoreApplication* qapp, const Options& options, QUrl url);
    void run(QUrl url);

private:
    QCoreApplication* app;

    Runtime* mRuntime;

signals:

public slots:
    void slTestingDone();
};

}

#endif // ARTEMISAPPLICATION_H
