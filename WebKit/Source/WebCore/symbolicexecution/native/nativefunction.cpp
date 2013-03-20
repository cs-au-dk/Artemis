#include "nativefunction.h"

#ifdef ARTEMIS

namespace SymbolicExecution
{

NativeFunction::NativeFunction(std::string name) :
    mName(name)
{
}

std::string NativeFunction::getName() const
{
    return mName;
}

}

#endif
