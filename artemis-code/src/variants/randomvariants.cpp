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
#include "randomvariants.h"
#include "events/forms/formfieldtypes.h"
#include <util/randomutil.h>

namespace artemis {

    RandomVariants::RandomVariants(ArtemisOptions* options) {
        Q_CHECK_PTR(options);
        this->opts = options;
    }

    BaseEventParameters RandomVariants::generate_base_event(QString type) {
        return BaseEventParameters(type,true,true);
    }

    KeyboardEventParameters RandomVariants::generate_keyboard_event(QString type) {
        KeyboardEventParameters res(type,
                                    true,
                                    true,
                                    QString("a"),
                                    0,
                                    false,
                                    false,
                                    false,
                                    false,
                                    false);
        return res;
    }

    MouseEventParameters RandomVariants::generate_mouse_event(QString type) {
        MouseEventParameters res(type,
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
        return res;
    }

    FormInput RandomVariants::generate_form_fields(const QSet<FormField>& fi) {
        FormInput res;
        foreach (FormField f,fi) {
            if (f.type() == TEXT) {
                res.add_field(f,FormFieldValue(generate_random_string(10)));
            } else if (f.type() == BOOLEAN) {
                res.add_field(f,FormFieldValue(random_bool()));
            } else if (f.type() == FIXED_INPUT) {
                res.add_field(f,FormFieldValue(pick_rand(f.inputs())));
            } else {
                res.add_field(f,FormFieldValue());
            }
        }
        return res;
    }

}
