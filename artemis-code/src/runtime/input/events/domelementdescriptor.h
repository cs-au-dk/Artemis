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
#ifndef DOMELEMENTDESCRIPTOR_H
#define DOMELEMENTDESCRIPTOR_H

#include <QObject>
#include <QtWebKit>
#include <QDebug>

#include "runtime/browser/artemiswebpage.h"

// TODO convert to new memory model

namespace artemis
{

class DOMElementDescriptor : public QObject
{
    Q_OBJECT

public:
    DOMElementDescriptor(QObject* parent, QWebElement* elm);
    DOMElementDescriptor(QObject* parent, const DOMElementDescriptor* other);

    QWebElement getElement(ArtemisWebPagePtr page) const;
    QString getTagName();
    QString getId();
    QString getClass();
    bool isInvalid() const;

    uint hashCode() const;
    QString toString() const;

    QDebug friend operator<<(QDebug dbg, const DOMElementDescriptor& e);

private:
    QString id;
    QString tagName;
    QString frameName;
    QString classLine;

    // Path from the mainFrame to the frame containig the element
    QList<int> framePath;

    // Path from the frame containing the element to the actual element
    QList<int> elementPath;

    // Special cases
    bool isDocument;// = false;
    bool isBody;// = false;
    bool isMainframe;// = false;
    bool mInvalid;

    void setFramePath(QWebElement* elm);
    void setElementPath(QWebElement* elm);

    QWebFrame* getFrame(ArtemisWebPagePtr page) const;
    QWebElement getElementFrame(QWebFrame* frame) const;
    QWebElement nthChild(QWebElement elm, int n) const;




};




}

#endif // DOMELEMENTDESCRIPTOR_H
