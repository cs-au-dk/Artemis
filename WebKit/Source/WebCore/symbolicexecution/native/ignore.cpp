#include "ignore.h"

#ifdef ARTEMIS

namespace SymbolicExecution
{

Ignore::Ignore(std::string name) :
    NativeFunction(),
    mName(name)
{
}

std::string Ignore::getName() const
{
    return mName;
}

}

#endif
