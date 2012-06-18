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

#include "timer.h"

namespace artemis {

  Timer::Timer() {
    
  }

  Timer::Timer(int id, int timeout, bool single_shot) {
      this->m_id = id;
      this->m_timeout = timeout;
      this->m_single_shot = single_shot;
  }
  
  Timer &Timer::operator=(const Timer &other) {
      this->m_id = other.m_id;
      this->m_timeout = other.m_timeout;
      this->m_single_shot = other.m_single_shot;
      return *this;
  }

  int Timer::get_id() const {
      return this->m_id;
  }

  int Timer::get_timeout() const {
      return this->m_timeout;
  }

  bool Timer::is_single_shot() const {
      return this->m_single_shot;
  }


}
