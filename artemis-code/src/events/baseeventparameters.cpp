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
#include "baseeventparameters.h"
#include "eventypes.h"
#include "util/randomutil.h"

namespace artemis {

    BaseEventParameters::BaseEventParameters(QString name, bool bubbles, bool cancelable)
    {
        Q_ASSERT(!name.isEmpty());
        this->name = name;
        this->bubbles = bubbles;
        this->cancelable = cancelable;
    }

    BaseEventParameters::BaseEventParameters() {

    }

    QString BaseEventParameters::js_string()  {
        if (!memo_js.isEmpty())
            return memo_js;
        QString rand_id = generate_random_js_id();
        QString res = "var " + rand_id + " = document.createEvent(\"Event\");";
        res = res + " " + rand_id + ".initEvent(";
        res += quote_string(name) = ",";
        res += bool_tostring(bubbles) + ",";
        res += bool_tostring(cancelable) + ",);";

        res += "this.dispatchEvent(" + rand_id + ");";

        memo_js = res;
        return res;
    }

    EventType BaseEventParameters::type() const {
        return BASE_EVENT;
    }

    BaseEventParameters::BaseEventParameters(const BaseEventParameters &other) {
        this->name = other.name;
        this->bubbles = other.bubbles;
        this->cancelable = other.cancelable;
    }

    BaseEventParameters& BaseEventParameters::operator=( BaseEventParameters &other) {
        this->name = other.name;
        this->bubbles = other.bubbles;
        this->cancelable = other.cancelable;
        return *this;
    }

    bool BaseEventParameters::operator ==( BaseEventParameters &other) {
        return (name == other.name)
                && (bubbles == other.bubbles)
                && (cancelable == other.cancelable);
    }

    bool BaseEventParameters::operator ==(EventParameters &other) {
        if (other.type() != type())
            return false;
        return *this == ((BaseEventParameters&)other);
    }

    QDebug  operator<<(QDebug dbg, const BaseEventParameters &e) {
        dbg.nospace() << "(name: " << e.name << ",bubbles: " << e.bubbles << ",cancelable: " << e.cancelable << ")" <<endl;
        return dbg.space();
    }

    uint BaseEventParameters::hashcode() const {
        return qHash(name)*17 + 7*(bubbles ? 1 : 0) + 23*(cancelable ? 1 : 0);
    }

}
