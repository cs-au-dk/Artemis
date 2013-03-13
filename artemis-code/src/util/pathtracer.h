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
#ifndef PATHTRACER_H
#define PATHTRACER_H
#include <string>
#include <iostream>
#include <QList>
#include <QPair>

using namespace std;
namespace artemis{

class PathTracer{
public:
    static void newPathTrace(QString event);
    static void functionCall(QString name);
    static void write();

private:
    enum ItemType {FUNCALL};
    typedef QPair<QString, QList<QPair<PathTracer::ItemType, QString> > > PathTrace;
    static QList<PathTrace> traces;
    static void appendItem(ItemType type, QString message);

};

}

#endif // PATHTRACER_H
