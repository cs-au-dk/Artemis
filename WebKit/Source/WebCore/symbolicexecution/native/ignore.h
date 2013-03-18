#ifndef IGNORE_H
#define IGNORE_H

#include "nativefunction.h"

#ifdef ARTEMIS

namespace SymbolicExecution
{

class Ignore : public NativeFunction
{

public:
    Ignore(std::string name);
    std::string getName() const;

private:
    std::string mName;

};

}

#endif
#endif // IGNORE_H
