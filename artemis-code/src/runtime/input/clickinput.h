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

#ifndef CLICKINPUT_H
#define CLICKINPUT_H


#include "baseinput.h"

namespace artemis {


/**
 * An input type which simulates a "real" user click on the page at a given XPath selector.
 * As with DomInput et al. this can also fill form values before executing the click.
 *
 * We need to have this class handle the XPath itself as the coordinates to click on need to be looked up each
 * iteration after the page has loaded (in case adverts, errors etc. have caused the entry point to move on the page).
 */
class ClickInput : public BaseInput
{
public:
    ClickInput(QString targetXPath,
               FormInputCollectionConstPtr formInput);

    void apply(ArtemisWebPagePtr page, QWebExecutionListener* webkitListener) const;
    BaseInputConstPtr getPermutation(const FormInputGeneratorConstPtr& formInputGenerator,
                                     const EventParameterGeneratorConstPtr& eventParameterGenerator,
                                     const TargetGeneratorConstPtr& targetGenerator,
                                     const ExecutionResultConstPtr& result) const;

    int hashCode() const;
    QString toString() const;

private:
    QString mTargetXPath;
    FormInputCollectionConstPtr mFormInput;
};

typedef QSharedPointer<const ClickInput> ClickInputConstPtr;

} // namespace artemis
#endif // CLICKINPUT_H
