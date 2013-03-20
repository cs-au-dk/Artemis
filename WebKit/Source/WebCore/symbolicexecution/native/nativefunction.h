#ifndef NATIVEFUNCTION_H
#define NATIVEFUNCTION_H

#include <string>

#ifdef ARTEMIS

namespace SymbolicExecution
{

class NativeFunction
{

public:
    NativeFunction();

    virtual std::string getName() const = 0;
};

}

#endif
#endif // NATIVEFUNCTION_H
