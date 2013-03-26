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

#ifndef ARTEMISWEBVIEW_H
#define ARTEMISWEBVIEW_H

#include <QObject>
#include <QWebView>
#include <QCloseEvent>
#include <QSharedPointer>

namespace artemis
{

class ArtemisWebView : public QWebView
{
    Q_OBJECT

public:
    explicit ArtemisWebView();

protected:
    void closeEvent(QCloseEvent* event);

signals:
    void sigClose();

};

typedef QSharedPointer<ArtemisWebView> ArtemisWebViewPtr;
typedef QSharedPointer<const ArtemisWebView> ArtemisWebViewConstPtr;

}

#endif // ARTEMISWEBVIEW_H
