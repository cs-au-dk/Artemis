/*
 * Copyright 2014 Aarhus University
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

#ifndef CVC4REGEXCOMPILER_H
#define CVC4REGEXCOMPILER_H

#include <string>

class CVC4RegexCompilerException {

public:
    CVC4RegexCompilerException(const std::string& what)
        : m_what(what) { }

    const char* what() const {
        return m_what.c_str();
    }

private:
    const std::string m_what;
};

class CVC4RegexCompiler
{

public:
    /**
     * @brief compile
     * @param javaScriptRegex A RAW JavaScript variant of regex.
     * @return An expression containing CVC4 constraints
     */
    static std::string compile(const std::string& javaScriptRegex, bool& bol, bool& eol);

private:
    CVC4RegexCompiler();
};

#endif // CVC4REGEXCOMPILER_H
