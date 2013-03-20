
#include <utility>

#include "JavaScriptCore/wtf/ExportMacros.h"
#include "JavaScriptCore/runtime/MathObject.h"

#include "ignore.h"
#include "nativelookup.h"

#ifdef ARTEMIS

namespace SymbolicExecution
{

NativeLookup::NativeLookup()
{

    mNativeFunctionMap.insert(std::make_pair<JSC::native_function_ID_t, NativeFunction*>(
                                  (JSC::native_function_ID_t)JSC::mathProtoFuncAbs,
                                  new Ignore("math.abs")));

}

const NativeFunction* NativeLookup::find(JSC::native_function_ID_t functionID)
{
    function_map_t::iterator iter = mNativeFunctionMap.find(functionID);
    return iter != mNativeFunctionMap.end() ? iter->second : NULL;
}

}

#endif
