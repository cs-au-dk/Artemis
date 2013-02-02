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
#include <QDebug>
#include "eventypes.h"

namespace artemis
{

EventType get_type(QString name)
{
    Q_ASSERT(!name.isEmpty());

    if (name == "click"
        || name == "dblclick"
        || name == "mousedown"
        || name == "mouseup"
        || name == "mouseover"
        || name == "mousemove"
        || name == "mouseout")
        { return MOUSE_EVENT; }

    if (name == "keypress"
        || name == "keydown"
        || name == "keyup")
        { return KEY_EVENT; }

    if (name == "readystatechange")
        { return AJAX_READY_STATE_CHANGE; }

    if (name == "focus"
        || name == "blur"
        || name == "submit"
        || name == "reset"
        || name == "select"
        || name == "change"
        || name == "resize")
        { return BASE_EVENT; }

    if (name == "load"
        || name == "DOMContentLoaded"
        || name == "DOMFrameContentLoaded"
        || name == "pageshow")
        { return LOAD_EVENT; }

    if (name == "unload"
        || name == "pagehide"
        || name == "beforeunload")
        { return UNLOAD_EVENT; }

    if (name == "touchstart"
        || name == "touchend"
        || name == "touchmove")
        { return TOUCH_EVENT; }

    if (name == "abort"
        || name == "error")
        { return NON_INTERACTIVE_EVENT; }

    return UNKNOWN_EVENT;
}

bool is_non_interactive(QString name)
{
    EventType t = get_type(name);
    return t == UNLOAD_EVENT || t == LOAD_EVENT || t == NON_INTERACTIVE_EVENT;
}
}
