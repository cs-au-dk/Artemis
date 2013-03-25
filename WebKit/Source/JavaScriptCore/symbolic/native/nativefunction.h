#ifndef NATIVEFUNCTION_H
#define NATIVEFUNCTION_H

#include <inttypes.h>
#include <string>

#ifdef ARTEMIS

namespace JSC
{

typedef intptr_t native_function_ID_t;

}

namespace Symbolic
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
