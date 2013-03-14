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

#include "manualruntime.h"

namespace artemis
{

ManualRuntime::ManualRuntime(QObject* parent, const Options& options, const QUrl& url) :
    Runtime(parent, options, url)
{

    mWebView = ArtemisWebViewPtr(new ArtemisWebView());
    mWebView->setPage(mWebkitExecutor->getPage().data());

    QObject::connect(mWebView.data(), SIGNAL(sigClose()),
                     this, SLOT(slWebViewClosed()));
}

void ManualRuntime::run(const QUrl& url)
{
   ExecutableConfigurationPtr initial =
        ExecutableConfigurationPtr(new ExecutableConfiguration(InputSequencePtr(new InputSequence()), url));

    mWebkitExecutor->executeSequence(initial);
    mWebView->show();
}

void ManualRuntime::slWebViewClosed()
{
    done();
}

}
