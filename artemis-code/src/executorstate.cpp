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
#include <QWebElement>

#include "executorstate.h"
#include "util/urlutil.h"

namespace artemis {

    ExecutorState::ExecutorState()
    {

    }

    QDebug operator<<(QDebug dbg, const ExecutorState &e) {
        dbg.nospace() << "Pages hashes: " << e.m_hash_to_dom;
        return dbg.space();
    }

    void ExecutorState::add_dom_state(QWebFrame* page) {
        // Translate all external pointing script tags to absolute URLs
        long hash = qHash(page->toHtml());
        //Possibly modifes the page.
        make_script_urls_absolute(page);
        this->m_hash_to_dom.insert(hash, page->toHtml());
    }

    QString ExecutorState::get_page_from_hash(long hash) const {
        Q_ASSERT(m_hash_to_dom.contains(hash));
        return m_hash_to_dom[hash];
    }

}
