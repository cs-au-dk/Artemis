/*
 *  Copyright (C) 2003, 2006, 2008 Apple Inc.
 *
 *  This library is free software; you can redistribute it and/or
 *  modify it under the terms of the GNU Library General Public
 *  License as published by the Free Software Foundation; either
 *  version 2 of the License, or (at your option) any later version.
 *
 *  This library is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 *  Library General Public License for more details.
 *
 *  You should have received a copy of the GNU Library General Public License
 *  along with this library; see the file COPYING.LIB.  If not, write to
 *  the Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
 *  Boston, MA 02110-1301, USA.
 *
 */

#include "config.h"
#include "ScopeChain.h"

#include <QSet>

#include "JSActivation.h"
#include "JSGlobalObject.h"
#include "JSObject.h"
#include "PropertyNameArray.h"
#include <stdio.h>
#include "Arguments.h"

namespace JSC {

ASSERT_HAS_TRIVIAL_DESTRUCTOR(ScopeChainNode);

#ifndef NDEBUG

void ScopeChainNode::print()
{
    ScopeChainIterator scopeEnd = end();
    for (ScopeChainIterator scopeIter = begin(); scopeIter != scopeEnd; ++scopeIter) {
        JSObject* o = scopeIter->get();
        PropertyNameArray propertyNames(globalObject->globalExec());
        o->methodTable()->getPropertyNames(o, globalObject->globalExec(), propertyNames, ExcludeDontEnumProperties);
        PropertyNameArray::const_iterator propEnd = propertyNames.end();

        fprintf(stderr, "----- [scope %p] -----\n", o);
        for (PropertyNameArray::const_iterator propIter = propertyNames.begin(); propIter != propEnd; propIter++) {
            Identifier name = *propIter;
            fprintf(stderr, "%s, ", name.ustring().utf8().data());
        }
        fprintf(stderr, "\n");
    }
}

#endif


#ifdef ARTEMIS
        QString ScopeChainNode::scopeChainAsJSON(JSFunction* function, ExecState* execState, QSet<QString>* visitedObjects){
            std::string retString = "{ \"parameters\":[";
            bool first = true;
            foreach(QString s, function->getArgumentsFromSourceCode(execState)){
                if(!first){
                    retString += ", ";
                }
                first = false;
                retString += "\""+s.toStdString() + "\"";
            }
            retString += "], \"arguments\":";

            JSValue arguments = execState->interpreter()->retrieveArguments(execState, function);

            retString += arguments.getAsJSONString(execState, visitedObjects).toStdString();

            ScopeChainIterator scopeEnd = end();
            retString += ", \"scope_chain\": [";
            int i = 0;
            for (ScopeChainIterator scopeIter = begin(); scopeIter != scopeEnd; ++scopeIter) {
                i++;
                qDebug() << i;
                JSObject* o = scopeIter->get();
                if(o == globalObject.get()){
                    continue;
                }
                if(retString.length() > 1){
                    retString += ", ";
                }
                retString += o->getAsJSONString(execState,visitedObjects).toStdString();
                /*
                retString += "{ \"#OBJECT_NAME#\":\""+o->classNameString().toStdString()+"\"";

                PropertyNameArray propertyNames(execState);
                o->methodTable()->getPropertyNames(o,execState, propertyNames, ExcludeDontEnumProperties);
                PropertyNameArray::const_iterator propEnd = propertyNames.end();
                for (PropertyNameArray::const_iterator propIter = propertyNames.begin(); propIter != propEnd; propIter++) {
                    Identifier name = *propIter;
                    QString strName = QString::fromStdString((std::string) name.ustring().utf8().data());
                    retString += ", \""+ strName.toStdString()+"\":"+ o->get(execState,name).getAsJSONString(execState, visitedObjects, true).toStdString();
                }
                retString +="}";
                */
            }
            retString += "]}";



            return QString::fromStdString(retString);
        }

#endif


const ClassInfo ScopeChainNode::s_info = { "ScopeChainNode", 0, 0, 0, CREATE_METHOD_TABLE(ScopeChainNode) };

int ScopeChainNode::localDepth()
{
    int scopeDepth = 0;
    ScopeChainIterator iter = this->begin();
    ScopeChainIterator end = this->end();
    while (!(*iter)->inherits(&JSActivation::s_info)) {
        ++iter;
        if (iter == end)
            break;
        ++scopeDepth;
    }
    return scopeDepth;
}

void ScopeChainNode::visitChildren(JSCell* cell, SlotVisitor& visitor)
{
    ScopeChainNode* thisObject = jsCast<ScopeChainNode*>(cell);
    ASSERT_GC_OBJECT_INHERITS(thisObject, &s_info);
    COMPILE_ASSERT(StructureFlags & OverridesVisitChildren, OverridesVisitChildrenWithoutSettingFlag);
    ASSERT(thisObject->structure()->typeInfo().overridesVisitChildren());
    if (thisObject->next)
        visitor.append(&thisObject->next);
    visitor.append(&thisObject->object);
    visitor.append(&thisObject->globalObject);
    visitor.append(&thisObject->globalThis);
}

} // namespace JSC
