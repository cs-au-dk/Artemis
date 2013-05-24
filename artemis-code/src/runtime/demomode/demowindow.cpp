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


#include "demowindow.h"

namespace artemis
{



DemoModeMainWindow::DemoModeMainWindow()
{
    mWebView = new QWebView(this);
    mWebView->load(QUrl("http://www.mistymountain.co.uk"));

    mAddressBar = new QLineEdit(this);
    mAddressBar->setSizePolicy(QSizePolicy::Expanding, mAddressBar->sizePolicy().verticalPolicy());
    connect(mAddressBar, SIGNAL(returnPressed()), SLOT(changeLocation()));

    QToolBar *toolBar = addToolBar(tr("Navigation"));
    toolBar->addAction(mWebView->pageAction(QWebPage::Back));
    toolBar->addAction(mWebView->pageAction(QWebPage::Forward));
    toolBar->addAction(mWebView->pageAction(QWebPage::Reload));
    toolBar->addAction(mWebView->pageAction(QWebPage::Stop));
    toolBar->addWidget(mAddressBar);

    setCentralWidget(mWebView);
}



}

