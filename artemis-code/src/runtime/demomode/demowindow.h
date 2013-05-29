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


#ifndef DEMOWINDOW_H
#define DEMOWINDOW_H



#include <QtGui>
#include <QLineEdit>
#include <QSharedPointer>
#include <QUrl>

#include "runtime/browser/artemiswebview.h"
#include "runtime/browser/webkitexecutor.h"
#include "artemisbrowserwidget.h"
#include "initialanalysiswidget.h"

namespace artemis
{



class DemoModeMainWindow : public QMainWindow
{
    Q_OBJECT

public:
    DemoModeMainWindow(WebKitExecutor *webkitExecutor, const QUrl& url);
    ~DemoModeMainWindow();

private:
    // Artemis
    ArtemisWebViewPtr mWebView;
    WebKitExecutor* mWebkitExecutor;

    // GUI
    // TODO: for some reason replacing these with QSharedPointer causes problems (in some cases).
    QToolBar* mToolBar;
    QLineEdit* mAddressBar;
    QProgressBar* mProgressBar;

    // The initial analysis panel is provided as its own widget.
    InitialAnalysisWidget* mInitialAnalysis;

    // The artemis browser widget.
    ArtemisBrowserWidget* mArtemisBrowser;


protected slots:
    void slChangeLocation();
    void slAdjustLocation();
    void slLoadStarted();
    void slLoadFinished(bool ok);
    void slSetProgress(int p);

signals:
    void sigClose();
};


typedef QSharedPointer<DemoModeMainWindow> DemoModeMainWindowPtr;

} // namespace artemis

#endif // DEMOWINDOW_H
