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

#include "cvc4regexcompiler.h"

#include <sstream>
#include <iostream>

#include "wtf/ExportMacros.h"
#include "wtf/Vector.h"
#include "JavaScriptCore/runtime/JSExportMacros.h"
#include "wtf/Platform.h"
#include "JavaScriptCore/yarr/Yarr.h"
#include "JavaScriptCore/yarr/YarrPattern.h"

std::string visitPatternAlternative(const JSC::Yarr::PatternAlternative*, bool& bol, bool& eol);
std::string visitPatternTerm(const JSC::Yarr::PatternTerm*, bool& bol, bool& eol);

std::string visitPatternDisjunction(const JSC::Yarr::PatternDisjunction* disjunction, bool& bol, bool& eol)
{
    std::stringstream result;

    if (disjunction->m_alternatives.size() > 1) {
        result << "(re.union ";
    }

    for (unsigned alt = 0; alt < disjunction->m_alternatives.size(); ++alt) {
        if (alt != 0) {
            result << " ";
        }

        JSC::Yarr::PatternAlternative* alternative = disjunction->m_alternatives[alt];
        result << visitPatternAlternative(alternative, bol, eol);
    }

    if (disjunction->m_alternatives.size() > 1) {
        result << ")";
    }

    return result.str();
}

std::string visitPatternAlternative(const JSC::Yarr::PatternAlternative* alternative, bool& bol, bool& eol)
{
    std::list<std::string> compiledTerms;

    for (unsigned i = 0; i < alternative->m_terms.size(); ++i) {

        std::stringstream compiledTerm;
        const JSC::Yarr::PatternTerm& term = alternative->m_terms[i];

        if (term.quantityType != JSC::Yarr::QuantifierFixedCount) {
            // Handle non-fixed results

            /*
             * TODO: Notice, we don't support the notion of greedy and non-greedy
             * term->quantityType == JSC::Yarr::QuantifierNonGreedy || term->quantityType == JSC::Yarr::QuantifierGreedy)
             */

            if (term.quantityCount.unsafeGet() == JSC::Yarr::quantifyInfinite) {
                compiledTerm << "(re.* " << visitPatternTerm(&term, bol, eol) << ")";

            } else if (term.quantityCount.unsafeGet() == 1) {
                compiledTerm << "(re.opt " << visitPatternTerm(&term, bol, eol) << ")";

            } else {

                compiledTerm << "(re.++";

                // insert 0 .. min concrete terms (already done before this term) and min .. max optional
                for (int i = 0; i < term.quantityCount.unsafeGet(); i++) {
                    compiledTerm << " (re.opt " << visitPatternTerm(&term, bol, eol) << ")";
                }

                compiledTerm << ")";

            }

        } else {
            // Handle fixed results

            if (term.quantityCount.unsafeGet() == 1) {
                compiledTerm << visitPatternTerm(&term, bol, eol);

            } else {
                // Remark: I don't know if its ever possible that quantityCount > 1 for fixed values
                // Similar terms (such as CC) are compiled into each their term with a quantity of 1

                compiledTerm << "(re.++";

                for (int i = 0; i < term.quantityCount.unsafeGet(); i++) {
                    compiledTerm << " " << visitPatternTerm(&term, bol, eol);
                }

                compiledTerm << ")";
            }

        }

        if (compiledTerm.str().size() > 0) {
            compiledTerms.push_back(compiledTerm.str());
        }
    }

    if (compiledTerms.size() == 0) {
        return "(str.to.re \"\")";
    }

    if (compiledTerms.size() == 1) {
        return compiledTerms.front();
    }

    std::stringstream result;
    result << "(re.++";

    while (!compiledTerms.empty()) {
        result << " " << compiledTerms.front();
        compiledTerms.pop_front();
    }

    result << ")";

    return result.str();
}

std::string visitPatternTerm(const JSC::Yarr::PatternTerm* term, bool& bol, bool& eol)
{
    // Special case for "." character class.
    if (term->m_invert && term->type == JSC::Yarr::PatternTerm::TypeCharacterClass &&
            term->characterClass->m_matches.size() == 2 &&
            term->characterClass->m_ranges.size() == 0 &&
            term->characterClass->m_matchesUnicode.size() == 2 &&
            term->characterClass->m_rangesUnicode.size() == 0 &&
            (char)term->characterClass->m_matches[0] == '\n' &&
            (char)term->characterClass->m_matches[1] == '\r')  {

        return "re.allchar";

    }


    if (term->m_invert) {
        throw CVC4RegexCompilerException("Unsupported usage of \"not\" in regex");
    }

    std::stringstream result;

    switch (term->type) {
    case JSC::Yarr::PatternTerm::TypeAssertionBOL:
        // Notice, the CVC4 constraint writer enforces BOL/EOL, not the regex compiler.
        // This allows for some constraint writer specific optimizations and tricks.
        //
        // We do not enforce the correct positioning of BOL/EOL!
        // We assume that they have been inserted in their correct position.

        bol = true;
        break;

    case JSC::Yarr::PatternTerm::TypeAssertionEOL:
        eol = true;
        break;

    case JSC::Yarr::PatternTerm::TypeAssertionWordBoundary:
        throw CVC4RegexCompilerException("Unsupported usage of word boundary in regex");
        break;

    case JSC::Yarr::PatternTerm::TypePatternCharacter: {
        if ((int)(term->patternCharacter) > 255) {
            std::stringstream str;
            str << "Unsupported usage of non-ascii characters (value " << (int)(term->patternCharacter) << " ) in regex";
            throw CVC4RegexCompilerException(str.str());
        }

        result << "(str.to.re \"" << CVC4RegexCompiler::escape((char)term->patternCharacter) << "\")";
        break;
    }

    case JSC::Yarr::PatternTerm::TypeCharacterClass: {

        if ((term->characterClass->m_ranges.size() + term->characterClass->m_matches.size()) == 0 &&
             (term->characterClass->m_matchesUnicode.size() > 0 || term->characterClass->m_rangesUnicode.size())) {
            throw CVC4RegexCompilerException("Unsupported usage of pure non-ascii characters in range regex");
        }

        // we omit all non-ascii characters from the range

        bool emitOnlyOne = (term->characterClass->m_ranges.size() + term->characterClass->m_matches.size()) == 1;

        if (!emitOnlyOne) {
            result << "(re.union";
        }

        for (size_t i = 0; i < term->characterClass->m_ranges.size(); ++i) {
            if (!emitOnlyOne) {
                result << " ";
            }

            result << "(re.range \"" << CVC4RegexCompiler::escape((char)term->characterClass->m_ranges[i].begin) << "\" \"" << \
                      CVC4RegexCompiler::escape((char)term->characterClass->m_ranges[i].end) << "\")";
        }

        for (size_t i = 0; i < term->characterClass->m_matches.size(); ++i) {
            if (!emitOnlyOne) {
                result << " ";
            }

            result << "(str.to.re \"" << CVC4RegexCompiler::escape((char)term->characterClass->m_matches[i]) << "\")";
        }

        if (!emitOnlyOne) {
            result << ")";
        }

        break;

    }

    case JSC::Yarr::PatternTerm::TypeBackReference:
        throw CVC4RegexCompilerException("Unsupported usage of back references in regex");
        break;

    case JSC::Yarr::PatternTerm::TypeForwardReference:
        throw CVC4RegexCompilerException("Unsupported usage of forward references in regex");
        break;

    case JSC::Yarr::PatternTerm::TypeParenthesesSubpattern:
        result << visitPatternDisjunction(term->parentheses.disjunction, bol, eol);
        break;

    case JSC::Yarr::PatternTerm::TypeParentheticalAssertion:
        throw CVC4RegexCompilerException("Unsupported usage of parenthetical-assertions, example of usage needed for implementation.)");
        break;

    case JSC::Yarr::PatternTerm::TypeDotStarEnclosure:
        throw CVC4RegexCompilerException("Unsupported usage of dotstar enclosure, example of usage needed for implementation.)");
        break;

    default:
        throw CVC4RegexCompilerException("Unknown pattern term encountered");
    }

    return result.str();
}

std::string CVC4RegexCompiler::compile(const std::string &javaScriptRegex, bool& bol, bool& eol)
{
    bol = false;
    eol = false;

    bool caseSensitivity = false;
    bool multiline = false;

    std::string input = javaScriptRegex;

    if (input.length() >= 2 && input.at(0) == '/' and input.at(input.length()-1) == '/') {
        // Strip "/ /" from regex
        input = input.substr(1, input.length()-2);
    }

    const char* m_constructionError = 0;
    JSC::Yarr::YarrPattern pattern(JSC::UString(input.c_str()), caseSensitivity, multiline, &m_constructionError);

    if (m_constructionError) {
        std::string err = "RegularExpression: YARR compile failed with: " + std::string(m_constructionError);
        throw CVC4RegexCompilerException(err);
    }

    return visitPatternDisjunction(pattern.m_body, bol, eol);
}

CVC4RegexCompiler::CVC4RegexCompiler()
{
}

std::string CVC4RegexCompiler::escape(const char c)
{
    std::stringstream result;

    int ci = (int)c;
    if ((ci >= 48 && ci <= 57) || (ci >= 65 && ci <= 90) || (ci >= 97 && ci <= 122)) { // a-z, A-Z, 0-9
        result << c;
    } else if (ci > 32 && ci < 127) {
        result << "\\" << c;
    } else {
        result << "\\x" << (ci < 16 ? "0" : "") << std::hex << ci; // emits \xYY where YY is the hex representation of the ascii char
    }

    return result.str();
}

std::string CVC4RegexCompiler::escape(const std::string& str)
{
    std::stringstream result;

    for (unsigned i = 0; i < str.length(); ++i) {
        result << CVC4RegexCompiler::escape(str.at(i));
    }

    return result.str();
}
