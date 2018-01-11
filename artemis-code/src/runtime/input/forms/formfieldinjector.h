/*
 * Copyright 2012 Aarhus University
 *
 * Licensed under the GNU General Public License, Version 3 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *          http://www.gnu.org/licenses/gpl-3.0.html
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#ifndef FORMFIELDINJECTOR_H
#define FORMFIELDINJECTOR_H

#include <QString>
#include <QDebug>
#include <QWebElement>

#include "injectionvalue.h"

namespace artemis
{

/**
 * A helper class for injecting new values into form fields.
 *
 * TODO: Make this class more specialised/robust for different input types.
 */

class FormFieldInjector
{
public:
    // Returns whether the injection was successful or not.
    static bool inject(QWebElement element, InjectionValue value);

    static bool injectAndTriggerChangeHandler(QWebElement element, InjectionValue value);
    static bool injectWithEventSimulation(QWebElement element, InjectionValue value, bool noBlur);

    static void triggerHandler(QWebElement element, QString eventName);
    static void triggerChangeHandler(QWebElement element);

    static void guiPressEnter(QWebElement element);

protected:
    static bool simulateTextFieldFilling(QWebElement element, QString value, bool noBlur);
    static bool simulateBooleanFieldFilling(QWebElement element, InjectionValue value, bool noBlur);
    static bool simulateSelectBoxFilling(QWebElement element, InjectionValue value, bool noBlur);

    static QString jsStringEscape(QString value);
};



} // namespace artemis
#endif // FORMFIELDINJECTOR_H
