#ifndef NATIVEFUNCTION_H
#define NATIVEFUNCTION_H

#include <string>

#ifdef ARTEMIS

namespace SymbolicExecution
{

class NativeFunction
{

public:
    NativeFunction(std::string name);

    virtual std::string getName() const;

private:
    std::string mName;
};

}

#endif
#endif // NATIVEFUNCTION_H
