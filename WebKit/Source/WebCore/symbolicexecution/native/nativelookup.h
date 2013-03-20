#ifndef NATIVELOOKUP_H
#define NATIVELOOKUP_H

#include <tr1/unordered_map>

#include "JavaScriptCore/artemisil/artemisil.h"

#include "nativefunction.h"

#ifdef ARTEMIS


namespace SymbolicExecution
{

class NativeLookup
{

public:
    NativeLookup();

    const NativeFunction* find(JSC::native_function_ID_t functionID);

private:
    typedef std::tr1::unordered_map<JSC::native_function_ID_t, NativeFunction*> function_map_t;
    function_map_t mNativeFunctionMap;

};

}

#endif
#endif // NATIVELOOKUP_H
