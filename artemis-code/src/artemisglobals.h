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
#ifndef ARTEMISGLOBALS_H
#define ARTEMISGLOBALS_H

#include <QtWebKit>
#include <string>
#include <sstream>

using namespace std;

namespace artemis
{

const QWebElement NULL_WEB_ELEMENT;
const QString ELEMENT_OBJECT_PLACEHOLDER = "%event_object%";
const QUrl DONT_MEASURE_COVERAGE("http://this-is-fake-dont-do-coverage.fake");

inline QString quote_string(const QString s)
{
    return "\"" + s + "\"";
}

inline QString bool_tostring(const bool b)
{
    return (b ? "true" : "false");
}

inline QString int_tostring(const int i)
{
    QString res = "";
    res.setNum(i);
    return res;
}

inline int hash_bool(int prime, bool b)
{
    return (b ? prime : 0);
}

inline string stdstr_to_int(int number)
{
    stringstream ss;
    ss << number;
    return ss.str();
}

inline bool is_omit(const QUrl& u)
{
    //TODO add support for exclusion of libraries!
    return u == DONT_MEASURE_COVERAGE;
}

}

#endif // ARTEMISGLOBALS_H
