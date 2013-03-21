#ifndef NATIVELOOKUP_H
#define NATIVELOOKUP_H

#include <tr1/unordered_map>
#include <tr1/unordered_set>

#include "JavaScriptCore/artemisil/artemisil.h"

#include "nativefunction.h"

namespace JSC {
    class ExecState;
}

namespace SymbolicExecution
{

class NativeLookup
{

public:
    NativeLookup();

    const NativeFunction* find(JSC::native_function_ID_t functionID);
    void buildRegistry(JSC::ExecState* callFrame);

private:

    typedef std::tr1::unordered_set<JSC::JSCell*> visited_t;
    void buildRegistryVisit(JSC::JSGlobalData* jsGlobalData, JSC::CallFrame* callFrame, JSC::JSObject* jsObject, visited_t* visited, std::string path);

    typedef std::tr1::unordered_map<JSC::native_function_ID_t, NativeFunction> function_map_t;
    function_map_t mNativeFunctionMap;

};

}

#endif // NATIVELOOKUP_H
