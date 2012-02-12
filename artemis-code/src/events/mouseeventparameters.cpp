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
#include "mouseeventparameters.h"
#include "artemisglobals.h"
#include "QString"
#include "util/randomutil.h"

namespace artemis {

    MouseEventParameters::MouseEventParameters(QString type, bool canBubble, bool cancelable,
                                               int detail, int screenX, int screenY, int clientX, int clientY,
                                               bool ctrlKey, bool altKey, bool  shiftKey, bool  metaKey,
                                               int button)
    {
        Q_ASSERT(!type.isEmpty());
        this->altKey = altKey;
        this->type_n = type;
        this->canBubble = canBubble;
        this->cancelable = cancelable;
        this->detail = detail;
        this->screenX = screenX;
        this->screenY = screenY;
        this->clientX = clientX;
        this->clientY = clientY;
        this->ctrlKey = ctrlKey;
        this->altKey = altKey;
        this->shiftKey = shiftKey;
        this->metaKey = metaKey;
        this->button = button;
    }


    MouseEventParameters::MouseEventParameters() {

    }

    MouseEventParameters::MouseEventParameters(const MouseEventParameters& other) {
        this->altKey = other.altKey;
        this->type_n = other.type_n;
        this->canBubble = other.canBubble;
        this->cancelable = other.cancelable;
        this->detail = other.detail;
        this->screenX = other.screenX;
        this->screenY = other.screenY;
        this->clientX = other.clientX;
        this->clientY = other.clientY;
        this->ctrlKey = other.ctrlKey;
        this->altKey = other.altKey;
        this->shiftKey = other.shiftKey;
        this->metaKey = other.metaKey;
        this->button = other.button;
    }


    /**
type
the string to set the event's type to. Possible types for mouse events include: click, mousedown, mouseup, mouseover, mousemove, mouseout.
canBubble
whether or not the event can bubble. Sets the value of event.bubbles.
cancelable
whether or not the event's default action can be prevented. Sets the value of event.cancelable.
view
the Event's AbstractView. You should pass the window object here. Sets the value of event.view.
detail
the Event's mouse click count. Sets the value of event.detail.
screenX
the Event's screen x coordinate. Sets the value of event.screenX.
screenY
the Event's screen y coordinate. Sets the value of event.screenY.
clientX
the Event's client x coordinate. Sets the value of event.clientX.
clientY
the Event's client y coordinate. Sets the value of event.clientY.
ctrlKey
whether or not control key was depressed during the Event. Sets the value of event.ctrlKey.
altKey
whether or not alt key was depressed during the Event. Sets the value of event.altKey.
shiftKey
whether or not shift key was depressed during the Event. Sets the value of event.shiftKey.
metaKey
whether or not meta key was depressed during the Event. Sets the value of event.metaKey.
button
the Event's mouse event.button.
relatedTarget
the Event's related EventTarget. Only used with some event types (e.g. mouseover and mouseout). In other cases, pass null.
      */
    QString MouseEventParameters::js_string() {
        if (!memo_js.isEmpty())
            return memo_js;
            
        QString rand_id = generate_random_js_id();
        QString res = "var " + rand_id + " = document.createEvent(\"MouseEvent\");";
        res = res + " " + rand_id + ".initMouseEvent(";
        res += quote_string(type_n) + ",";
        res += bool_tostring(canBubble) + ",";
        res += bool_tostring(cancelable) + ",";
        res += "window,";
        res += int_tostring(detail) + ",";
        res += int_tostring(screenX) + ",";
        res += int_tostring(screenY) + ",";
        res += int_tostring(clientX) + ",";
        res += int_tostring(clientY) + ",";
        res += bool_tostring(ctrlKey) + ",";
        res += bool_tostring(altKey) + ",";
        res += bool_tostring(shiftKey) + ",";
        res += bool_tostring(metaKey) + ",";
        res += int_tostring(button) + ",";
        res += "null);";

        res +=  "this.dispatchEvent(" + rand_id + ");";

        memo_js = res;
        return res;
    }

    EventType MouseEventParameters::type() const{
        return MOUSE_EVENT;
    }

    MouseEventParameters &MouseEventParameters::operator=( MouseEventParameters &other) {
        this->altKey = other.altKey;
        this->type_n = other.type_n;
        this->canBubble = other.canBubble;
        this->cancelable = other.cancelable;
        this->detail = other.detail;
        this->screenX = other.screenX;
        this->screenY = other.screenY;
        this->clientX = other.clientX;
        this->clientY = other.clientY;
        this->ctrlKey = other.ctrlKey;
        this->altKey = other.altKey;
        this->shiftKey = other.shiftKey;
        this->metaKey = other.metaKey;
        this->button = other.button;
        return *this;
    }

    bool MouseEventParameters::operator==(MouseEventParameters &other) {
       return (altKey == other.altKey)
               && (type_n == other.type_n)
               && (canBubble == other.canBubble)
               && (cancelable == other.cancelable)
               && (detail == other.detail)
               && (screenX == other.screenX)
               && (screenY == other.screenY)
               && (clientX == other.clientX)
               && (clientY == other.clientY)
               && (ctrlKey == other.ctrlKey)
               && (altKey = other.altKey)
               && (shiftKey == other.shiftKey)
               && (metaKey == other.metaKey)
               && (button = other.button);
    }

    bool MouseEventParameters::operator ==(EventParameters &other) {
        if (other.type() != type())
            return false;
        return *this == ((MouseEventParameters&)other);
    }

    QDebug operator<<(QDebug dbg, const MouseEventParameters &e) {
        dbg.nospace() << "(name: " << e.type_n << ",bubbles: " << e.canBubble << ",cancelable: " << e.cancelable << ",button " << e.button << ")" <<endl;
        return dbg.space();
    }

    uint MouseEventParameters::hashcode() const {
        return hash_bool(7,altKey) + qHash(type_n)*13 + hash_bool(31,canBubble)
                + hash_bool(11,cancelable) + 3*detail + 5*screenX + 17*screenY + 19*clientX
                + 23*clientY + hash_bool(29,ctrlKey) + hash_bool(37,altKey) + hash_bool(41,shiftKey) + hash_bool(43,metaKey)
                + 47*button;
    }

}
