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

#include <QWebElement>
#include <QList>

#include "events/eventhandlerdescriptor.h"
#include "inputgenerator/targets/jquerylistener.h"
#include "util/randomutil.h"

#include "jquerytarget.h"

namespace artemis {
  
  JQueryTarget::JQueryTarget(EventHandlerDescriptor& event_handler,  ArtemisOptions* options) : TargetDescriptor(event_handler) { 
      artemis_options = options;
  }
  /*JQueryTarget::JQueryTarget(TargetDescriptor* other) : TargetDescriptor(other) { }*/

  QString JQueryTarget::get_signature(QWebElement element) {
      if (element.isNull()) {
          return QString("");
      }

      QString result = get_signature(element.parent());

      if (element.tagName() == QString("HTML")) {
          result = result.append("#document.HTML");
      } else {
          result = result.append(element.tagName());
      }
      
      result = result.append(QString("."));

      return result;
  }

  QWebElement JQueryTarget::get(ArtemisWebPage* page) {

      QString signature = get_signature(m_event_handler->dom_element().get_element(page));
      QString event = m_event_handler->name();

      qDebug() << "TARGET::Info, looking for selectors for signature " << signature << " and event " << event << endl;

      JQueryListener* listener = artemis_options->get_jquery_listener();

      QList<QString> selectors = listener->lookup(signature, event);

      if (selectors.count() == 0) {
          qDebug() << "TARGET::Warning, no matching selectors found, defaulting to source" << endl;
          return m_event_handler->dom_element().get_element(page);
      }

      /* Select random selector */
      QString selector = pick_rand(selectors);

      /* Select target element */
      QWebElementCollection elements = page->currentFrame()->findAllElements(selector);

      if (elements.count() == 0) {
          qDebug() << "TARGET::Warning, no matching elements found, defaulting to source" << endl;
          return m_event_handler->dom_element().get_element(page);
      
      } else {
          QWebElement element = pick_rand(elements.toList());

          QString name = element.tagName();
          qDebug() << "TARGET::Selecting element " << name << " out of a total of " << elements.count() << "element(s) and " << selectors.count() << " selector(s)" << endl;
          
          return element;
      }
  }
}