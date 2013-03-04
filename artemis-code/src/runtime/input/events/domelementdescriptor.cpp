/*
 * Copyright 2012 Aarhus University
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <QtWebKit>
#include <QtGlobal>
#include <artemisglobals.h>
#include <QHash>

#include "domelementdescriptor.h"

namespace artemis
{

DOMElementDescriptor::DOMElementDescriptor(QObject* parent, QWebElement* elm) : QObject(parent)
{
    Q_CHECK_PTR(elm);

    this->mInvalid = false;

    //Q_ASSERT((*elm) != NULL_WEB_ELEMENT);
    if (elm->isNull()) {
        //Asume document
        this->isDocument = true;
        this->isMainframe = true;
        this->tagName = "<document>";
        this->frameName = "<mainframe>";
    }
    else {
        this->id = elm->attribute("id");
        this->tagName = elm->tagName();
        this->classLine = QString(elm->classes().join(" "));
        //this->frameName = elm->webFrame()->frameName();
        isBody = isDocument = isMainframe = false;
        //setFramePath(elm);
        setElementPath(elm);
    }
}

DOMElementDescriptor::DOMElementDescriptor(QObject* parent, const DOMElementDescriptor* other) : QObject(parent)
{
    this->elementPath = QList<int>(other->elementPath);
    this->framePath = QList<int>(other->framePath);
    this->id = other->id;
    this->tagName = other->tagName;
    this->classLine = other->classLine;
    //this->frameName = other.frameName;
    this->isBody = other->isBody;
    this->isDocument = other->isDocument;
    this->isMainframe = other->isMainframe;
    this->mInvalid = other->mInvalid;
}

QWebElement DOMElementDescriptor::getElement(ArtemisWebPagePtr page) const
{
    Q_CHECK_PTR(page);
    QWebFrame* frame = getFrame(page);
    QWebElement elm = getElementFrame(frame);
    Q_ASSERT(elm != NULL_WEB_ELEMENT);
    return elm;
}

QString DOMElementDescriptor::getTagName()
{
    return this->tagName;
}

QString DOMElementDescriptor::getId()
{
    return this->id;
}

QString DOMElementDescriptor::getClass()
{
    return this->classLine;
}

QWebFrame* DOMElementDescriptor::getFrame(ArtemisWebPagePtr page) const
{
    Q_CHECK_PTR(page);

    if (isMainframe)
        { return page->mainFrame(); }

    QWebFrame* current = page->mainFrame();
    foreach(int id, framePath) {
        current = current->childFrames().at(id);
    }
    Q_CHECK_PTR(current);
    return current;
}

QWebElement DOMElementDescriptor::getElementFrame(QWebFrame* frame) const
{
    Q_CHECK_PTR(frame);

    if (isDocument)
        { return frame->documentElement(); }

    if (isBody) {
        QWebElement body = frame->findFirstElement("body");
        Q_ASSERT(body != NULL_WEB_ELEMENT);
        return body;
    }

    QWebElement current = frame->findFirstElement("body");
    Q_ASSERT(current != NULL_WEB_ELEMENT);
    // qDebug() << "Trying to get element: " << elementPath << *this;
    foreach(int id, elementPath) {
        current = nthChild(current, id);

        if (current == NULL_WEB_ELEMENT) {
            qDebug() << "Invalid frame path: " << *this;
            return QWebElement();
        }
    }
    return current;
}

QWebElement DOMElementDescriptor::nthChild(QWebElement elm, int n) const
{
    QWebElement currentChild = elm.firstChild();
    //qDebug() << "1" << currentChild.tagName();
    int i = 1;

    while (i < n) {
        currentChild = currentChild.nextSibling();
        //qDebug() << "2" << currentChild.tagName();
        i++;
    }

    return currentChild;
}

void DOMElementDescriptor::setFramePath(QWebElement* elm)
{
    QWebFrame* elementFrame = elm->webFrame();
    QWebPage* page = elementFrame->page();
    QWebFrame* mainFrame = page->mainFrame();

    if (elementFrame == mainFrame) {
        isMainframe = true;
        return;
    }

    // Q_ASSERT(false);
    QWebFrame* parent = elementFrame->parentFrame();
    QWebFrame* current = elementFrame;

    while (parent != mainFrame) {
        framePath.prepend(parent->childFrames().indexOf(current));
        current = parent;
        parent = parent->parentFrame();

        if (parent == 0) {
            this->mInvalid = true;
            break;
        }
    }
}

void DOMElementDescriptor::setElementPath(QWebElement* elm)
{
    if (elm->tagName() == "body") {
        isBody = true;
        return;
    }
    else if (elm->tagName() == "document" || elm->tagName().toLower() == "html") {
        isDocument = true;
        return;
    }

    QWebElement document = elm->document();
    QWebElement parent = elm->parent();
    QWebElement current = *elm;

    //qDebug() << "Starting setElementPath for \n" << elm->toOuterXml()  <<"\nEND\n";
    while (parent != document) {
        int index = 0;
        QWebElement c = parent.firstChild();

        //  qDebug() << "!><! \n" << parent.toOuterXml() << "\nEND\n";
        if (c == NULL_WEB_ELEMENT) {
            this->mInvalid = true;
            break;
        }

        while (c != current) {
            index++;
            c = c.nextSibling();

            if (c == NULL_WEB_ELEMENT) {
                this->mInvalid = true;
                break;
            }
        }

        elementPath.prepend(index + 1);
        current = parent;
        parent = parent.parent();

        //qDebug() << "Is null: " << parent.isNull();
        if (parent == NULL_WEB_ELEMENT) {
            this->mInvalid = true;
            break;
        }
    }
}

bool DOMElementDescriptor::isInvalid() const
{
    return this->mInvalid;
}

uint DOMElementDescriptor::hashCode() const {

    uint frame_hash = 0;

    if (isMainframe) {
        frame_hash = 7;
    } else {
        foreach (int fpath, framePath) {
            frame_hash = fpath + 17 * frame_hash;
        }
    }

    uint element_hash = 0;

    if (isDocument) {
        element_hash = 23;
    } else if (isBody) {
        element_hash = 7;
    } else {
        foreach (int element, elementPath) {
            element_hash = element + 23 * element_hash;
        }
    }

    return 29 * element_hash + 13 * frame_hash;
}

QString DOMElementDescriptor::toString() const
{
    QString elmName = "";

    if (!id.isEmpty()) {
        elmName = id;
    }
    else if (isBody) {
        elmName = "body";
    }
    else if (isDocument) {
        elmName = "document";
    }
    else {
        elmName = tagName;
    }

    return elmName;
}

QDebug operator<<(QDebug dbg, const DOMElementDescriptor& e)
{
    QString elmName = "";

    if (!e.id.isEmpty()) {
        elmName = e.id;
    }
    else if (e.isBody)
        { elmName = "body"; }
    else if (e.isDocument)
        { elmName = "document"; }
    else
        { elmName = e.tagName; }

    //Include frame info?
    dbg.nospace() << elmName;
    return dbg.space();
}

}
