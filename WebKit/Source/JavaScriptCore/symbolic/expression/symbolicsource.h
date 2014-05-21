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

#ifndef SYMBOLICSOURCE_H
#define SYMBOLICSOURCE_H

#include <strings.h>

namespace Symbolic {

enum SourceIdentifierMethod {
    INPUT_NAME, ELEMENT_ID
};

enum SourceType {
    TEXT, SELECT, SELECT_INDEX, RADIO, CHECKBOX, UNKNOWN
};

class SymbolicSource
{

public:
    SymbolicSource(SourceType type, SourceIdentifierMethod identifier_method, std::string identifier) :
        m_type(type),
        m_identifier_method(identifier_method),
        m_identifier(identifier) {
    }

    inline SourceType getType() const {
        return m_type;
    }

    inline SourceIdentifierMethod getIdentifierMethod() const {
        return m_identifier_method;
    }

    inline std::string getIdentifier() const {
        return m_identifier;
    }

    static SourceType stringAccessTypeAttrToSourceType(const char * type) {
        if(strncasecmp(type, "select", 6) == 0){
            return SELECT;
        }
        return TEXT;
    }

    // Removed the int SourceType lookup function for two reasons.
    // 1) We currently only generate ints for select box selectedIndex lookups.
    // 2) Select boxes are not identified by type attribute anyway, they are a separate element. So this code was returning UNKNOWN anyway.
    /*
    static SourceType intAccessTypeAttrToSourceType(const char * type) {
        if(strncasecmp(type, "select", 6) == 0){
            return SELECT_INDEX;
        }
        return UNKNOWN;
    }
    */

    static SourceType boolAccessTypeAttrToSourceType(const char * type) {
        if(strncasecmp(type, "radio", 5) == 0){
            return RADIO;
        }
        if(strncasecmp(type, "checkbox", 8) == 0){
            return CHECKBOX;
        }
        return UNKNOWN;
    }

private:
    SourceType m_type;
    SourceIdentifierMethod m_identifier_method;
    std::string m_identifier;

};

}

#endif // SYMBOLICSOURCE_H
