#ifndef SYMBOLICSOURCE_H
#define SYMBOLICSOURCE_H

namespace Symbolic {

enum SourceIdentifierMethod {
    INPUT_NAME, ELEMENT_ID
};

enum SourceType {
    INPUT
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

private:
    SourceType m_type;
    SourceIdentifierMethod m_identifier_method;
    std::string m_identifier;

};

}

#endif // SYMBOLICSOURCE_H
