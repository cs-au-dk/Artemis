/*
 * Copyright 2012 Aarhus University
 *
 * Licensed under the GNU General Public License, Version 3 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *          http://www.gnu.org/licenses/gpl-3.0.html
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <QtWebKit>
#include <artemisglobals.h>
#include <QHash>
#include <QDebug>

#include "domelementdescriptor.h"

namespace artemis
{

const QWebElement NULL_WEB_ELEMENT;

DOMElementDescriptor::DOMElementDescriptor(QWebElement* elm) :
    mIsDocument(false),
    mIsBody(false),
    mIsMainframe(false),
    mInvalid(false)
{
    Q_CHECK_PTR(elm);

    if (elm->isNull()) {
        // Asume document

        mIsDocument = true;
        mIsMainframe = true;

        mTagName = "<document>";

    } else {
        mId = elm->attribute("id");
        mName = elm->attribute("name");
        mTagName = elm->tagName();
        mClassLine = QString(elm->classes().join(" "));

        //setFramePath(elm);
        setElementPath(elm);
    }
}

QWebElement DOMElementDescriptor::getElement(ArtemisWebPagePtr page) const
{
    QWebFrame* frame = selectFrame(page);
    QWebElement elm = selectElement(frame);

    Q_ASSERT(elm != NULL_WEB_ELEMENT);
    return elm;
}

QWebFrame* DOMElementDescriptor::selectFrame(ArtemisWebPagePtr page) const
{
    if (mIsMainframe) {
        return page->mainFrame();
    }

    QWebFrame* current = page->mainFrame();
    foreach(int id, mFramePath) {
        current = current->childFrames().at(id);
    }

    Q_CHECK_PTR(current);
    return current;
}

QWebElement DOMElementDescriptor::selectElement(QWebFrame* frame) const
{
    Q_CHECK_PTR(frame);

    if (mIsDocument) {
        return frame->documentElement();
    }

    if (mIsBody) {
        QWebElement body = frame->findFirstElement("body");
        Q_ASSERT(body != NULL_WEB_ELEMENT);
        return body;
    }

    QWebElement current = frame->findFirstElement("body");
    Q_ASSERT(current != NULL_WEB_ELEMENT);

    foreach(int id, mElementPath) {
        current = selectNthChild(current, id);

        if (current == NULL_WEB_ELEMENT) {
            qDebug() << "ERROR: Invalid DOM element descriptor applied to web page";
            return QWebElement();
        }
    }

    return current;
}

QWebElement DOMElementDescriptor::selectNthChild(QWebElement elm, int n) const
{
    QWebElement currentChild = elm.firstChild();

    int i = 1;
    while (i < n) {
        currentChild = currentChild.nextSibling();
        i++;
    }

    return currentChild;
}

/*
void DOMElementDescriptor::setFramePath(QWebElement* elm)
{
    QWebFrame* elementFrame = elm->webFrame();
    QWebPage* page = elementFrame->page();
    QWebFrame* mainFrame = page->mainFrame();

    if (elementFrame == mainFrame) {
        mIsMainframe = true;
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
*/

void DOMElementDescriptor::setElementPath(QWebElement* elm)
{
    if (elm->tagName() == "body") {
        mIsBody = true;
        return;

    }

    if (elm->tagName() == "document" || elm->tagName().toLower() == "html") {
        mIsDocument = true;
        return;
    }

    QWebElement document = elm->document();
    QWebElement parent = elm->parent();
    QWebElement current = *elm;

    while (parent != document) {
        int index = 0;
        QWebElement c = parent.firstChild();

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

        mElementPath.prepend(index + 1);
        current = parent;
        parent = parent.parent();

        if (parent == NULL_WEB_ELEMENT) {
            this->mInvalid = true;
            break;
        }
    }
}

uint DOMElementDescriptor::hashCode() const {

    uint frame_hash = 0;

    if (mIsMainframe) {
        frame_hash = 7;
    } else {
        foreach (int fpath, mFramePath) {
            frame_hash = fpath + 17 * frame_hash;
        }
    }

    uint element_hash = 0;

    if (mIsDocument) {
        element_hash = 23;
    } else if (mIsBody) {
        element_hash = 7;
    } else {
        foreach (int element, mElementPath) {
            element_hash = element + 23 * element_hash;
        }
    }

    return 29 * element_hash + 13 * frame_hash;
}

QString DOMElementDescriptor::toString() const
{
    QString elmName = "";

    if (!mId.isEmpty()) {
        elmName = mId;
    }
    else if (mIsBody) {
        elmName = "body";
    }
    else if (mIsDocument) {
        elmName = "document";
    }
    else {
        elmName = mTagName;
    }

    return elmName;
}

}
