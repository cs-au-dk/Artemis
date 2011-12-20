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
#include "deterministicworklist.h"
#include <stdlib.h>

namespace artemis {

    DeterministicWorkList::DeterministicWorkList() :
            WorkList()
    {
        queue.clear();
        largest_pri = 0;
    }

    void DeterministicWorkList::add(const ExecutableConfiguration e, int priority) {
        QSet<ExecutableConfiguration> *set = queue.value(priority);
        //qDebug() << "Adding: " << e.hashcode() << "with " << priority;
        if (set == 0) {
            set = new QSet<ExecutableConfiguration>();
            queue.insert(priority,set);
        }
        set->insert(e);
        if (priority > largest_pri) {
            largest_pri = priority;
        }
    }

    ExecutableConfiguration DeterministicWorkList::remove() {
        QSet<ExecutableConfiguration> *set = queue.value(largest_pri);
        if (set == 0)
            qDebug() << "PANIC!";
        Q_CHECK_PTR(set);
        Q_ASSERT(!set->isEmpty());
        ExecutableConfiguration res = set->toList().at(rand() % set->size());
        set->remove(res);
        if (set->isEmpty()) {
            queue.remove(largest_pri);
            delete set;
            largest_pri = queue.empty() ? 0 : queue.keys().last();
        }
        return res;
    }

    bool DeterministicWorkList::all_zero_priority() {
       return largest_pri == 0;
    }

    int DeterministicWorkList::size() {
        int res = 0;
        foreach (int k, queue.keys()) {
            res += queue.value(k)->size();
        }
        return res;
    }

    bool DeterministicWorkList::empty() {
        return queue.empty();
    }

     bool DeterministicWorkList::contains(const ExecutableConfiguration& e) {
         foreach (int k, queue.keys()) {
             if (queue.value(k)->contains(e))
                 return true;
         }
         return false;
     }

    void DeterministicWorkList::new_priority(const ExecutableConfiguration& e, int priority) {
        foreach (int k, queue.keys()) {
            if (queue.value(k)->contains(e)) {
                queue.value(k)->remove(e);
            }
        }
        add(e,priority);
    }

    QString DeterministicWorkList::toString() {
        //TODO
    }
}
