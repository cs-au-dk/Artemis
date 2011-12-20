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
#include "executableconfiguration.h"

namespace artemis {

    ExecutableConfiguration::ExecutableConfiguration() {

    }

    ExecutableConfiguration::ExecutableConfiguration(EventSequence seq, QUrl start_url)
    {
        this->url = start_url;
        this->sequence = seq;
    }

    ExecutableConfiguration::ExecutableConfiguration(const ExecutableConfiguration& other)
    {
        this->url = other.url;
        this->sequence = other.sequence;
    }

    QUrl ExecutableConfiguration::starting_url() const {
        return url;
    }

    ExecutableConfiguration ExecutableConfiguration::copy_with_sequence(const EventSequence seq) const {
        return ExecutableConfiguration(seq,this->starting_url());
    }

    ExecutableConfiguration::~ExecutableConfiguration() {

    }

    bool ExecutableConfiguration::operator==(ExecutableConfiguration& rhs) const {
        return this->sequence == rhs.sequence;
    }

    bool ExecutableConfiguration::is_initial() {
       return sequence.empty();
    }

    EventSequence ExecutableConfiguration::get_eventsequence() const{
        return this->sequence;
    }

    uint ExecutableConfiguration::hashcode() const {
        return qHash(url.toString())* 17 + sequence.hashcode()*11;
    }

    ExecutableConfiguration& ExecutableConfiguration::operator=(const ExecutableConfiguration &other) {
        this->url = other.url;
        this->sequence = other.sequence;
        return *this;
    }

  /*  QString ExecutableConfiguration::toSimpleString() {
        QString res;
        res = "Eventsequence: " +  sequence.toSimpleString();
        res = "\nStart url: " + url->toString();
        return res;
    }*/

}


