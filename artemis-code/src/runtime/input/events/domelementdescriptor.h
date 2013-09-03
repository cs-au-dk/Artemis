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

#include <QSharedPointer>

#include "runtime/browser/artemiswebpage.h"

namespace artemis
{

/**
 * This class represents a DOM element in a web page across executions.
 *
 * Use this to save the location of DOM element A in execution AE, and
 * to find the corresponding DOM element B in execution BE.
 */
class DOMElementDescriptor
{

public:
    DOMElementDescriptor(QWebElement* elm);

    QWebElement getElement(ArtemisWebPagePtr page) const;

    inline bool isInvalid() const {
        return mInvalid;
    }

    inline QString getTagName() const {
        return mTagName;
    }

    inline QString getName() const {
        return mName;
    }

    inline QString getId() const {
        return mId;
    }

    inline QString getArtemisFormIdentifier() const {
        return mArtemisFormIdentifier;
    }

    inline QString getClass() const {
        return mClassLine;
    }

    uint hashCode() const;
    QString toString() const;

private:
    // Stored attributes
    QString mId;
    QString mTagName;
    QString mName;
    QString mClassLine;

    QString mArtemisFormIdentifier; // only used for form fields

    // Path from the mainFrame to the frame containig the element
    QList<int> mFramePath;

    // Path from the frame containing the element to the actual element
    QList<int> mElementPath;

    // Special cases
    bool mIsDocument;
    bool mIsBody;
    bool mIsMainframe;
    bool mInvalid;

    // NOTE, the frame path is not used since it caused some stability issues - and none of our examples require the frame path
    // See the constructor for the disabled call to this function
    //void setFramePath(QWebElement* elm);
    void setElementPath(QWebElement* elm);

    QWebFrame* selectFrame(ArtemisWebPagePtr page) const;
    QWebElement selectElement(QWebFrame* frame) const;
    QWebElement selectNthChild(QWebElement elm, int n) const;
};

typedef QSharedPointer<DOMElementDescriptor> DOMElementDescriptorPtr;
typedef QSharedPointer<const DOMElementDescriptor> DOMElementDescriptorConstPtr;

}

#endif // DOMELEMENTDESCRIPTOR_H
