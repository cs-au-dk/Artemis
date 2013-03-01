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
#include <QDebug>
#include <execinfo.h>
#include <stdlib.h>

#include "exceptionhandlingqapp.h"

ExceptionHandlingQApp::ExceptionHandlingQApp(int& c, char** v): QApplication(c, v) {}

bool ExceptionHandlingQApp::notify(QObject* rec, QEvent* ev)
{
    try {
        return QApplication::notify(rec, ev);
    }
    catch (char const* str) {
        qDebug() << "EXCEPTION: " << str;
        return false;
    }
    catch (std::exception& e) {
        void* array[20];
        size_t size = backtrace(array, 20);

        qCritical() << "Exception thrown:" << e.what();
        backtrace_symbols_fd(array, size, 2);

        exit(1);
    }

    return false;
}
