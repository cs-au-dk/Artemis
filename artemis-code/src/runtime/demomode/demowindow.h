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
#include <QWebView>
#include <QLineEdit>
#include <QSharedPointer>


namespace artemis
{




class DemoModeMainWindow : public QMainWindow
{
    Q_OBJECT

public:
    DemoModeMainWindow();

protected slots:

private:
    QWebView *mWebView;
    QLineEdit *mAddressBar;

};


typedef QSharedPointer<DemoModeMainWindow> DemoModeMainWindowPtr;

} // namespace artemis

#endif // DEMOWINDOW_H
