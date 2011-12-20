/*
 * Copyright (C) Research In Motion Limited 2010. All rights reserved.
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Library General Public
 * License as published by the Free Software Foundation; either
 * version 2 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Library General Public License for more details.
 *
 * You should have received a copy of the GNU Library General Public License
 * along with this library; see the file COPYING.LIB.  If not, write to
 * the Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
 * Boston, MA 02110-1301, USA.
 */

#ifndef RenderSVGShadowTreeRootContainer_h
#define RenderSVGShadowTreeRootContainer_h

#if ENABLE(SVG)
#include "RenderSVGTransformableContainer.h"

namespace WebCore {
    
class SVGUseElement;
class SVGShadowTreeRootElement;

class RenderSVGShadowTreeRootContainer : public RenderSVGTransformableContainer {
public:
    RenderSVGShadowTreeRootContainer(SVGUseElement*);
    virtual ~RenderSVGShadowTreeRootContainer();

    virtual bool isSVGShadowTreeRootContainer() const { return true; }

    void markShadowTreeForRecreation() { m_recreateTree = true; }
    void updateStyle(Node::StyleChange);
    virtual void updateFromElement();

    Node* rootElement() const;

private:
    virtual void styleDidChange(StyleDifference, const RenderStyle* oldStyle);

    bool m_recreateTree;
    RefPtr<SVGShadowTreeRootElement> m_shadowRoot;
};

}

#endif
#endif
