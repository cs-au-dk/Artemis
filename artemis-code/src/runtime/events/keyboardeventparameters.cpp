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
#include "keyboardeventparameters.h"
#include "artemisglobals.h"
#include "util/randomutil.h"

namespace artemis {

    //KeyboardEventParameters::KeyboardEventParameters() {}

    KeyboardEventParameters::KeyboardEventParameters(QString eventType, bool canBubble, bool cancelable,
                                                     QString keyIdentifier,  unsigned int keyLocation,
                                                     bool ctrlKey, bool altKey, bool shiftKey, bool metaKey, bool altGraphKey)
    {
        Q_ASSERT(!eventType.isEmpty());
        this->eventType = eventType;
        this->canBubble = canBubble;
        this->cancelable = cancelable;
        this->keyIdentifier = keyIdentifier;
        this->keyLocation = keyLocation;
        this->ctrlKey = ctrlKey;
        this->altKey = altKey;
        this->shiftKey = shiftKey;
        this->metaKey = metaKey;
        this->altGraphKey = altGraphKey;
    }

    KeyboardEventParameters::KeyboardEventParameters() {

    }

    QString KeyboardEventParameters::js_string() {
        if (!memo_js.isEmpty())
            return memo_js;
        QString rand_id = generate_random_js_id();
        QString res = "var " + rand_id + " = document.createEvent(\"KeyboardEvent\");";
        res = res + " " + rand_id + ".initKeyboardEvent(";
        res += eventType + ",";
        res += bool_tostring(canBubble) + ",";
        res += bool_tostring(cancelable) + ",";
        res += "null,";
        res += quote_string(keyIdentifier) + ",";
        res += keyLocation + ",";
        res += bool_tostring(ctrlKey) + ",";
        res += bool_tostring(altKey) + ",";
        res += bool_tostring(shiftKey) + ",";
        res += bool_tostring(metaKey) + ",";
        res += bool_tostring(altGraphKey) + ");";

        res += "this.dispatchEvent(" + rand_id + ");";

        memo_js = res;
        return res;
    }

    EventType KeyboardEventParameters::type() const {
        return KEY_EVENT;
    }

    KeyboardEventParameters::KeyboardEventParameters(const KeyboardEventParameters &other) {
        this->eventType = other.eventType;
        this->canBubble = other.canBubble;
        this->keyIdentifier = other.keyIdentifier;
        this->keyLocation = other.keyLocation;
        this->ctrlKey = other.ctrlKey;
        this->altKey = other.altKey;
        this->shiftKey = other.shiftKey;
        this->metaKey = other.metaKey;
        this->altGraphKey = other.altGraphKey;
        this->cancelable = other.cancelable;
    }

    KeyboardEventParameters &KeyboardEventParameters::operator=( KeyboardEventParameters &other) {
        this->eventType = other.eventType;
        this->canBubble = other.canBubble;
        this->keyIdentifier = other.keyIdentifier;
        this->keyLocation = other.keyLocation;
        this->ctrlKey = other.ctrlKey;
        this->altKey = other.altKey;
        this->shiftKey = other.shiftKey;
        this->metaKey = other.metaKey;
        this->altGraphKey = other.altGraphKey;
        this->cancelable = other.cancelable;
        return *this;
    }

    bool KeyboardEventParameters::operator==(KeyboardEventParameters &other) {
        return eventType == other.eventType &&
                canBubble == other.canBubble &&
                keyIdentifier == other.keyIdentifier &&
                keyLocation == other.keyLocation &&
                ctrlKey == other.ctrlKey &&
                altKey == other.altKey &&
                shiftKey == other.shiftKey &&
                metaKey == other.metaKey &&
                altGraphKey == other.altGraphKey &&
                cancelable == other.cancelable;
    }

    bool KeyboardEventParameters::operator ==(EventParameters &other) {
        if (other.type() != type())
            return false;
        return *this == ((KeyboardEventParameters&)other);
    }

    QDebug operator<<(QDebug dbg, const KeyboardEventParameters &e) {
        dbg.nospace() << "(name: " << e.eventType << ",bubbles: " << e.canBubble << ",cancelable: " << e.cancelable << ",button " << e.keyIdentifier << ")" <<endl;
        return dbg.space();
    }

    uint KeyboardEventParameters::hashcode() const {
        return hash_bool(7,altKey) + qHash(eventType)*13 + hash_bool(31,canBubble)
                + hash_bool(11,cancelable) + hash_bool(29,ctrlKey) + hash_bool(37,altKey) + hash_bool(41,shiftKey) + hash_bool(43,metaKey)
                + 47*qHash(keyIdentifier) + 17*keyLocation +hash_bool(23,altGraphKey);
    }

}
