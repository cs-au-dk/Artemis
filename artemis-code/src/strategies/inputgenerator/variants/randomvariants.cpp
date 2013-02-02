/*
  Copyright 2011 Simon Holm Jensen. All rights reserved.

  Redistribution and use in source and binary forms, with or without modification, are
  permitted provided that the following conditions are met:

     1. Redistributions of source code must retain the above copyright notice, this list of
        conditions and the following disclaimer.

     2. Redistributions in binary form must reproduce the above copyright notice, this list
        of conditions and the following disclaimer in the documentation and/or other materials
        provided with the distribution.

  THIS SOFTWARE IS PROVIDED BY SIMON HOLM JENSEN ``AS IS'' AND ANY EXPRESS OR IMPLIED
  WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND
  FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL <COPYRIGHT HOLDER> OR
  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
  CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
  SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
  ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
  NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
  ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

  The views and conclusions contained in the software and documentation are those of the
  authors and should not be interpreted as representing official policies, either expressed
  or implied, of Simon Holm Jensen
*/

#include <assert.h>
#include <util/randomutil.h>

#include "runtime/events/baseeventparameters.h"
#include "runtime/events/keyboardeventparameters.h"
#include "runtime/events/mouseeventparameters.h"
#include "runtime/events/forms/formfieldtypes.h"
#include "runtime/events/forms/forminput.h"

#include "randomvariants.h"

namespace artemis
{

RandomVariants::RandomVariants() : VariantsGenerator()
{

}

EventParameters* RandomVariants::generateEventParameters(QObject* parent, const EventHandlerDescriptor* eventHandler)
{

    switch (eventHandler->getEventType()) {

    case BASE_EVENT:
        return new BaseEventParameters(parent, eventHandler->name(), true, true);
        break;

    case MOUSE_EVENT:
        return new MouseEventParameters(parent, eventHandler->name(),
                                        true,
                                        true,
                                        1,
                                        0,
                                        0,
                                        0,
                                        0,
                                        false,
                                        false,
                                        false,
                                        false,
                                        0);
        break;

    case KEY_EVENT:
        return new KeyboardEventParameters(parent, eventHandler->name(),
                                           true,
                                           true,
                                           QString("a"),
                                           0,
                                           false,
                                           false,
                                           false,
                                           false,
                                           false);
        break;

    default:
        qFatal("Unknown event type!");
        assert(false);
    }
}

FormInput* RandomVariants::generateFormFields(QObject* parent, const QSet<FormField*>& fields)
{
    FormInput* result = new FormInput(parent);

    foreach(FormField * field, fields) {

        FormField* formField = new FormField(parent, field);

        switch (formField->type()) {
        case TEXT:
            result->addInput(formField, new FormFieldValue(parent, generateRandomString(10)));
            break;
        case BOOLEAN:
            result->addInput(formField, new FormFieldValue(parent, randomBool()));
            break;
        case FIXED_INPUT:
            result->addInput(formField, new FormFieldValue(parent, pickRand(formField->inputs())));
            break;
        default:
            result->addInput(formField, new FormFieldValue(parent));
        }
    }

    return result;
}

}
