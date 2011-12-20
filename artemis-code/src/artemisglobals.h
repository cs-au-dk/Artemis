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

namespace artemis {

    class FormInput;
    class EventDescriptor;
    class SourceInfo;

    const QWebElement NULL_WEB_ELEMENT;
    const QString ELEMENT_OBJECT_PLACEHOLDER = "%event_object%";
    const QUrl DONT_MEASURE_COVERAGE("http://this-is-fake-dont-do-coverage.fake");

    const char INDEX_HEADER_A[] = {
    #include "index-header.dat"
    };
    const QString INDEX_HEADER(INDEX_HEADER_A);

    const char INDEX_FOOTER_A[] = {
    #include "index-footer.dat"
    };
    const QString INDEX_FOOTER(INDEX_FOOTER_A);

    inline QString quote_string(const QString s) {
        return "\"" + s + "\"";
    }

    inline QString bool_tostring(const bool b) {
        return (b ? "true" : "false");
    }

    inline QString int_tostring(const int i) {
        QString res = "";
        res.setNum(i);
        return res;
    }

    inline int hash_bool(int prime, bool b) {
        return (b ? prime : 0);
    }

    inline string stdstr_to_int(int number)
    {
       stringstream ss;
       ss << number;
       return ss.str();
    }

    inline bool is_omit(const QUrl& u) {
        //TODO add support for exclusion of libraries!
        return u == DONT_MEASURE_COVERAGE;
    }
}

uint qHash(const artemis::FormInput &key);
uint qHash(const artemis::EventDescriptor &d);

inline uint qHash(const QList<int> &l)
{
    int hashcode = 1;
    foreach(int i, l)
        hashcode = 31*hashcode + i;
    return hashcode;
}

inline uint qHash(const QSet<int> &l)
{
    int hashcode = 1;
    foreach(int i, l)
        hashcode = 23*hashcode + i;
    return hashcode;
}


template <typename T>
inline uint qHash(const QSet<T> c) {
    int hashcode = 1;
    foreach(T i, c)
        hashcode = 23*hashcode + qHash(i);
    return hashcode;
}

template <typename T>
inline uint qHash(const QList<T> c) {
    int hashcode = 1;
    foreach(T i, c)
        hashcode = 17*hashcode + qHash(i);
    return hashcode;
}

template <typename T, typename R>
inline uint qHash(const QMap<R,T> c) {
    QMapIterator<R, T> iter(c);
    uint hash = 0;
    while(iter.hasNext()) {
        iter.next();
        hash = 23*hash + qHash(iter.value());
    }
    return hash;
}



#endif // ARTEMISGLOBALS_H
