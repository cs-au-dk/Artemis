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
#include "domelementdescriptor.h"
#include <QtWebKit>
#include <QtGlobal>
#include <artemisglobals.h>
#include <QHash>


namespace artemis {

    DOMElementDescriptor::DOMElementDescriptor(QWebElement *elm)
    {
        Q_CHECK_PTR(elm);
        this->m_invalid = false;
        //Q_ASSERT((*elm) != NULL_WEB_ELEMENT);
        if (elm->isNull()) {
            //Asume document
            this->is_document = true;
            this->is_mainframe = true;
            this->tag_name = "<document>";
            this->frame_name = "<mainframe>";
        } else {
            this->id = elm->attribute("id");
            this->tag_name = elm->tagName();
            this->class_line = QString(elm->classes().join(" "));
            //this->frame_name = elm->webFrame()->frameName();
            is_body = is_document = is_mainframe = false;
            //set_frame_path(elm);
            set_element_path(elm);
        }
    }

    DOMElementDescriptor::DOMElementDescriptor(const DOMElementDescriptor &other) {
        this->element_path = QList<int>(other.element_path);
        this->frame_path = QList<int>(other.frame_path);
        this->id = other.id;
        this->tag_name = other.tag_name;
        this->class_line = other.class_line;
        //this->frame_name = other.frame_name;
        this->is_body = other.is_body;
        this->is_document = other.is_document;
        this->is_mainframe = other.is_mainframe;
    }

    QWebElement DOMElementDescriptor::get_element(QWebPage *page) {
        Q_CHECK_PTR(page);
        QWebFrame* frame = get_frame(page);
        QWebElement elm = get_element_frame(frame);
        Q_ASSERT(elm != NULL_WEB_ELEMENT);
        return elm;
    }

    QString DOMElementDescriptor::get_tag_name() {
        return this->tag_name;
    }

    QString DOMElementDescriptor::get_id() {
        return this->id;
    }

    QString DOMElementDescriptor::get_class() {
        return this->class_line;
    }

    QWebFrame* DOMElementDescriptor::get_frame(QWebPage *page) {
        Q_CHECK_PTR(page);
        if (is_mainframe)
            return page->mainFrame();
        QWebFrame* current = page->mainFrame();
        foreach (int id, frame_path) {
            current = current->childFrames().at(id);
        }
        Q_CHECK_PTR(current);
        return current;
    }

    QWebElement DOMElementDescriptor::get_element_frame(QWebFrame *frame) {
        Q_CHECK_PTR(frame);
        if (is_document)
            return frame->documentElement();
        if (is_body) {
            QWebElement body = frame->findFirstElement("body");
            Q_ASSERT(body != NULL_WEB_ELEMENT);
            return body;
        }
        QWebElement current = frame->findFirstElement("body");
        Q_ASSERT(current != NULL_WEB_ELEMENT);
        // qDebug() << "Trying to get element: " << element_path << *this;
        foreach(int id, element_path) {
            current = nth_child(current,id);
            if (current == NULL_WEB_ELEMENT) {
                qDebug() << "Invalid frame path: " << *this;
                return QWebElement();
            }
        }
        return current;
    }

    QWebElement DOMElementDescriptor::nth_child(QWebElement elm,int n) {
        QWebElement current_child = elm.firstChild();
        //qDebug() << "1" << current_child.tagName();
        int i = 1;
        while (i < n) {
            current_child = current_child.nextSibling();
            //qDebug() << "2" << current_child.tagName();
            i++;
        }
        return current_child;
    }

    QDebug operator<<(QDebug dbg, const DOMElementDescriptor &e) {
        QString elm_name = "";
        if (!e.id.isEmpty()) {
            elm_name = e.id;
        }
        else if (e.is_body)
            elm_name = "body";
        else if (e.is_document)
            elm_name = "document";
        else
            elm_name = e.tag_name;
        //Include frame info?
        dbg.nospace() << elm_name;
        return dbg.space();
    }

    bool DOMElementDescriptor::operator==(DOMElementDescriptor& other) {
        bool frame_equals = false;
        bool element_equals = false;
        if (is_mainframe && other.is_mainframe)
            frame_equals = true;
        else
            frame_equals = frame_path == other.frame_path;
        if ((is_body && other.is_body) || (is_document && other.is_document))
            element_equals = true;
        else
            element_equals = element_path == other.element_path;
        return frame_equals && element_equals;
    }

    void DOMElementDescriptor::set_frame_path(QWebElement* elm) {
        QWebFrame* element_frame = elm->webFrame();
        QWebPage* page = element_frame->page();
        QWebFrame* main_frame = page->mainFrame();

        if (element_frame == main_frame) {
            is_mainframe = true;
            return;
        }
       // Q_ASSERT(false);
        QWebFrame* parent = element_frame->parentFrame();
        QWebFrame* current = element_frame;
        while (parent != main_frame) {
            frame_path.prepend(parent->childFrames().indexOf(current));
            current = parent;
            parent = parent->parentFrame();
            if (parent == 0) {
                this->m_invalid = true;
                break;
            }
        }
    }

    void DOMElementDescriptor::set_element_path(QWebElement* elm) {
        if (elm->tagName() == "body") {
            is_body = true;
            return;
        } else if (elm->tagName() == "document" || elm->tagName().toLower() == "html") {
            is_document = true;
            return;
        }

        QWebElement document = elm->document();
        QWebElement parent = elm->parent();
        QWebElement current = *elm;
        int i = 0;
        //qDebug() << "Starting set_element_path for \n" << elm->toOuterXml()  <<"\nEND\n";
        while (parent != document) {
            int index = 0;
            QWebElement c = parent.firstChild();
          //  qDebug() << "!><! \n" << parent.toOuterXml() << "\nEND\n";
            if (c == NULL_WEB_ELEMENT) {
                this->m_invalid = true;
                break;
            }
            while (c != current) {
                index++;
                c = c.nextSibling();
                if (c == NULL_WEB_ELEMENT) {
                    this->m_invalid = true;
                    break;
                }
            }
            element_path.prepend(index+1);
            current = parent;
            parent = parent.parent();
            //qDebug() << "Is null: " << parent.isNull();
            if (parent == NULL_WEB_ELEMENT) {
                this->m_invalid = true;
                break;
            }
        }
    }

    bool DOMElementDescriptor::is_invalid() {
        return this->m_invalid;
    }

    uint DOMElementDescriptor::hashcode() const {
        uint frame_hash = 0;
        uint element_hash = 0;
        if (is_mainframe)
            frame_hash = 31;
        else
            frame_hash = 31 * qHash(frame_path);
        if (is_document)
            element_hash = 23;
        else if (is_body)
            element_hash = 7;
        else
            element_hash = 7 *qHash(element_path);
        return 29*element_hash + 13*frame_hash;
    }

}
