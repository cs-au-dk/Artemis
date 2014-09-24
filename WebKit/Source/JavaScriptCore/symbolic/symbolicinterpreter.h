/*
 * Copyright 2012 Aarhus University
 *
 * Licensed under the GNU General Public License, Version 3 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *          http://www.gnu.org/licenses/gpl-3.0.html
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#ifndef SYMBOLICINTERPRETER_H
#define SYMBOLICINTERPRETER_H

#include <sstream>

#include "WTF/wtf/ExportMacros.h"
#include "JavaScriptCore/instrumentation/bytecodeinfo.h"

#include "native/nativelookup.h"

#ifdef ARTEMIS

#define SSTR(x) dynamic_cast< std::ostringstream & >( \
        ( std::ostringstream() << std::dec << x ) ).str()

namespace JSC {
    class ExecState;
    class Instruction;
}

namespace Symbolic
{

extern unsigned int NEXT_SYMBOLIC_ID;

typedef enum {
    EQUAL, NOT_EQUAL, STRICT_EQUAL, NOT_STRICT_EQUAL, LESS_EQ, LESS_STRICT, GREATER_EQ, GREATER_STRICT,
    ADD, SUBTRACT, MULTIPLY, DIVIDE, MODULO
} OP;

const char* opToString(OP op);

/*WTF_EXPORT_PRIVATE*/ class SymbolicInterpreter
{

public:
    SymbolicInterpreter();

    void ail_call(JSC::ExecState* callFrame, const JSC::Instruction* vPC, JSC::BytecodeInfo& info);
    void ail_call_native(JSC::ExecState* callFrame, const JSC::Instruction* vPC, JSC::BytecodeInfo& info,
                         JSC::native_function_ID_t functionID);

    JSC::JSValue ail_op_binary(JSC::ExecState* callFrame, const JSC::Instruction* vPC, JSC::BytecodeInfo& info,
                               JSC::JSValue& x, OP op, JSC::JSValue& y, JSC::JSValue result);

    void ail_jmp_iff(JSC::ExecState* callFrame, const JSC::Instruction* vPC, JSC::BytecodeInfo& info,
                     JSC::JSValue& condition, bool jumps);

    // called from the interpreter before it starts executing (a single trace)
    void preExecution(JSC::ExecState* callFrame);

    /*
     * Called from Artemis
     */
    void beginSession();
    void endSession();

    /*
     *  Global bit which is set when a op_get_by_val is called with a symbolic value.
     *  This is used to identify symbolic calls to lookup functions from the WebKit<->JavaScript layer,
     *  which does not get any symbolic information about lookup properties and indexes.
     *
     *  We could have expanded the APIs to send the original JSValue (with symbolic inforamtion) to the
     *  API layer, but it would require a lot of changes to a very central part of WebKit. This "hack"
     *  allows us to access the data globally without changing the existing APIs.
     */
    static bool isOpGetByValWithSymbolicArg() {
        return SymbolicInterpreter::m_isOpGetByValWithSymbolicArg;
    }

    static void setOpGetByValWithSymbolicArg(bool val) {
        SymbolicInterpreter::m_isOpGetByValWithSymbolicArg = val;
    }

    /*
     * Feature bits.
     *
     * These are set by Artemis directly, to disable internal features for benchmarking purposes.
     */
    static bool isFeatureSymbolicSelectedIndexEnabled() {
        return SymbolicInterpreter::m_featureSymbolicSelectedIndexEnabled;
    }
    static void setFeatureSymbolicSelectedIndexEnabled(bool value) {
        SymbolicInterpreter::m_featureSymbolicSelectedIndexEnabled = value;
    }

    static bool isFeatureIndirectOptionIndexLookupEnabled() {
        return SymbolicInterpreter::m_featureIndirectOptionIndexLookupEnabled;
    }
    static void setFeatureIndirectOptionIndexLookupEnabled(bool value) {
        SymbolicInterpreter::m_featureIndirectOptionIndexLookupEnabled = value;
    }

private:
    void fatalError(JSC::CodeBlock* codeBlock, std::string reason) __attribute__((noreturn));

    NativeLookup m_nativeFunctions;
    int m_nextSymbolicValue;

    bool m_inSession;
    bool m_shouldGC;

    static bool m_isOpGetByValWithSymbolicArg;

    // Feature flags
    static bool m_featureSymbolicSelectedIndexEnabled;
    static bool m_featureIndirectOptionIndexLookupEnabled;
};

}

#endif
#endif // SYMBOLICINTERPRETER_H
