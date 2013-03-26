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

#ifndef MANUALRUNTIME_H
#define MANUALRUNTIME_H

#include <QObject>

#include "runtime/browser/artemiswebview.h"

#include "runtime/runtime.h"

namespace artemis
{

class ManualRuntime : public Runtime
{

    Q_OBJECT

public:
    ManualRuntime(QObject* parent, const Options& options, const QUrl& url);

    void run(const QUrl& url);

protected:

    ArtemisWebViewPtr mWebView;

private slots:

    void slWebViewClosed();

};

}

#endif // MANUALRUNTIME_H
