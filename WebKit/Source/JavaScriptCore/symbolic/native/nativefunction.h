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

#ifndef NATIVEFUNCTION_H
#define NATIVEFUNCTION_H

#ifdef ARTEMIS

#include <inttypes.h>
#include <string>

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
    std::string m_name;
};

}

#endif
#endif // NATIVEFUNCTION_H
