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

#include "util/loggingutil.h"

namespace artemis
{



DemoModeMainWindow::DemoModeMainWindow(WebKitExecutor* webkitExecutor, const QUrl &url) :
    mWebkitExecutor(webkitExecutor)
{
    Log::info("DEMO: Constructing main window.");
    mWebView = ArtemisWebViewPtr(new ArtemisWebView());
    mWebView->setPage(mWebkitExecutor->getPage().data());

    QObject::connect(mWebView.data(), SIGNAL(loadStarted()),
                     this, SLOT(slLoadStarted()));
    QObject::connect(mWebView.data(), SIGNAL(loadFinished(bool)),
                     this, SLOT(slLoadFinished(bool)));
    QObject::connect(mWebView.data(), SIGNAL(loadFinished(bool)),
                     this, SLOT(slAdjustLocation()));

    // The address bar for artemis' browser.
    mAddressBar = new QLineEdit(this);
    mAddressBar->setSizePolicy(QSizePolicy::Expanding, mAddressBar->sizePolicy().verticalPolicy());
    mAddressBar->setText(url.toString());
    QObject::connect(mAddressBar, SIGNAL(returnPressed()),
                     this, SLOT(slChangeLocation()));

    // Toolbar used to control the artemis browser instance.
    mToolBar = addToolBar(tr("Navigation"));
    mToolBar->addAction(mWebView->pageAction(QWebPage::Back));
    mToolBar->addAction(mWebView->pageAction(QWebPage::Forward));
    mToolBar->addAction(mWebView->pageAction(QWebPage::Reload));
    mToolBar->addAction(mWebView->pageAction(QWebPage::Stop));
    mToolBar->addWidget(mAddressBar);

    // Progress bar for artemis' browser.
    mProgressBar = new QProgressBar(this);
    mProgressBar->setRange(0,100);
    mProgressBar->setFixedWidth(100);
    slSetProgress(0);
    mToolBar->addWidget(mProgressBar);
    QObject::connect(mWebView.data(), SIGNAL(loadProgress(int)),
                     this, SLOT(slSetProgress(int)));


    // TODO: This is not the central widget (with others docked around it. We want a more sophisticated layout.
    setCentralWidget(mWebView.data());



    // TODO: all the above is temp and needs to move into ArtemisBrowserWidget.
/*
    // The layout manager for this window.
    QHBoxLayout* layout = new QHBoxLayout();

    // Initial analysis results from artemis.
    mInitialAnalysis = new InitialAnalysisWidget(this);
    layout->addWidget(mInitialAnalysis);

    // Browser widget displaying Artemis' browser.
    mArtemisBrowser = new ArtemisBrowserWidget(this);
    layout->addWidget(mArtemisBrowser);

    // Set up this window.
    setLayout(layout);
    resize(1024, 768);
    setWindowTitle("Artemis Demonstration Mode");

    //setCentralWidget(initialAnalysis);
*/
}

DemoModeMainWindow::~DemoModeMainWindow()
{
    Log::info("DEMO: Destroying main window.");
    // Do not delete mWebkitExecutor, that is managed from elsewhere.
    delete mAddressBar;
    delete mToolBar;
    delete mProgressBar;
    delete mInitialAnalysis;
    emit sigClose();
}



// Called when we choose a new page via the loaction bar.
void DemoModeMainWindow::slChangeLocation()
{
    Log::info(QString("DEMO: Changed loaction to %1").arg(mAddressBar->text()).toStdString());
    QUrl url = QUrl(mAddressBar->text());
    mWebView->load(url);
    mWebView->setFocus();
}

// Called when we need to update the contents of the address bar.
void DemoModeMainWindow::slAdjustLocation()
{
    mAddressBar->setText(mWebView->url().toString());
    Log::info(QString("DEMO: Adjusted loaction to %1").arg(mWebView->url().toString()).toStdString());
}


// Called when we begin loading a page.
void DemoModeMainWindow::slLoadStarted()
{
    Log::info("DEMO: Begin page load.");
}

// Called when we finish loading a page.
void DemoModeMainWindow::slLoadFinished(bool ok)
{
    Log::info("DEMO: Finished page load.");
}

// Called when the page loading progress needs to be updated.
void DemoModeMainWindow::slSetProgress(int p)
{
    Log::info(QString("DEMO: Updating page load progress: %1%").arg(p).toStdString());
    mProgressBar->setValue(p);
    if(p >= 100){
        mProgressBar->setFormat("Loaded.");
    }else{
        mProgressBar->setFormat("Loading: %p%");
    }
}

}

