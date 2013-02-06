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
#ifndef MOUSEEVENTPARAMETERS_H
#define MOUSEEVENTPARAMETERS_H

#include "eventparameters.h"

namespace artemis
{

class MouseEventParameters : public EventParameters
{
public:
    MouseEventParameters(QObject* parent, QString type, bool canBubble, bool cancelable,
                         int detail, int screenX, int screenY, int clientX, int clientY,
                         bool ctrlKey, bool altKey, bool  shiftKey, bool  metaKey,
                         int button);

    QString jsString() const;
    EventType type() const;

    bool canBubble;
    bool cancelable;
    int detail;
    int screenX;
    int screenY;
    int clientX;
    int clientY;
    bool ctrlKey;
    bool altKey;
    bool shiftKey;
    bool metaKey;
    int button;
    QString typeN;

private:
    mutable QString cachedJsString;

};

}
#endif // MOUSEEVENTPARAMETERS_H
