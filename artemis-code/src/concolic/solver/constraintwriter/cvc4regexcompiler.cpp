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

#include "wtf/ExportMacros.h"
#include "JavaScriptCore/runtime/JSExportMacros.h"
#include "wtf/Platform.h"
#include "JavaScriptCore/yarr/Yarr.h"
#include "JavaScriptCore/yarr/YarrPattern.h"

std::string visitPatternAlternative(const JSC::Yarr::PatternAlternative*);
std::string visitPatternTerm(const JSC::Yarr::PatternTerm*);


std::string visitPatternDisjunction(const JSC::Yarr::PatternDisjunction* disjunction)
{
    std::stringstream result;

    if (disjunction->m_alternatives.size() > 1) {
        result << "(re.or ";
    }

    for (unsigned alt = 0; alt < disjunction->m_alternatives.size(); ++alt) {
        if (alt != 0) {
            result << " ";
        }

        JSC::Yarr::PatternAlternative* alternative = disjunction->m_alternatives[alt];
        result << visitPatternAlternative(alternative);
    }

    if (disjunction->m_alternatives.size() > 1) {
        result << ")";
    }

    return result.str();
}

std::string visitPatternAlternative(const JSC::Yarr::PatternAlternative* alternative)
{
    std::stringstream result;

    if (alternative->m_terms.size() == 0) {
        return "(str.to.re \"\")";
    }

    if (alternative->m_terms.size() > 1) {
        result << "(re.++ ";
    }

    for (unsigned i = 0; i < alternative->m_terms.size(); ++i) {
        if (i != 0) {
            result << " ";
        }

        const JSC::Yarr::PatternTerm& term = alternative->m_terms[i];


        if (term.quantityType != JSC::Yarr::QuantifierFixedCount) {
            // Handle non-fixed results

            /*
             * TODO: Notice, we don't support the notion of greedy and non-greedy
             * term->quantityType == JSC::Yarr::QuantifierNonGreedy || term->quantityType == JSC::Yarr::QuantifierGreedy)
             */

            if (term.quantityCount.unsafeGet() == JSC::Yarr::quantifyInfinite) {
                result << "(re.* " << visitPatternTerm(&term) << ")";

            } else if (term.quantityCount.unsafeGet() == 1) {
                result << "(re.opt " << visitPatternTerm(&term) << ")";

            } else {

                result << "(re.++";

                // insert 0 .. min concrete terms (already done before this term) and min .. max optional
                for (int i = 0; i < term.quantityCount.unsafeGet(); i++) {
                    result << " (re.opt " << visitPatternTerm(&term) << ")";
                }

                result << ")";

            }

        } else {
            // Handle fixed results

            if (term.quantityCount.unsafeGet() == 1) {
                result << visitPatternTerm(&term);

            } else {
                // Remark: I don't know if its ever possible that quantityCount > 1 for fixed values
                // Similar terms (such as CC) are compiled into each their term with a quantity of 1

                result << "(re.++";

                for (int i = 0; i < term.quantityCount.unsafeGet(); i++) {
                    result << " " << visitPatternTerm(&term);
                }

                result << ")";
            }

        }
    }

    if (alternative->m_terms.size() > 1) {
        result << ")";
    }

    return result.str();
}

std::string visitPatternTerm(const JSC::Yarr::PatternTerm* term)
{
    std::stringstream result;

    switch (term->type) {
    case JSC::Yarr::PatternTerm::TypeAssertionBOL:
        throw CVC4RegexCompilerException("Unsupported usage of ^ in regex");
        break;

    case JSC::Yarr::PatternTerm::TypeAssertionEOL:
        throw CVC4RegexCompilerException("Unsupported usage of $ in regex");
        break;

    case JSC::Yarr::PatternTerm::TypeAssertionWordBoundary:
        throw CVC4RegexCompilerException("Unsupported usage of word boundary in regex");
        break;

    case JSC::Yarr::PatternTerm::TypePatternCharacter: {
        if ((int)(term->patternCharacter) > 255) {
            throw CVC4RegexCompilerException("Unsupported usage of non-ascii characters in regex");
        }

        result << "(str.to.re \"" << (char)term->patternCharacter << "\")";
        break;
    }

    case JSC::Yarr::PatternTerm::TypeCharacterClass:

        if (term->characterClass->m_matchesUnicode.size() > 0 || term->characterClass->m_rangesUnicode.size()) {
            throw CVC4RegexCompilerException("Unsupported usage of non-ascii characters in range regex");
        }

        result << "CC";
        // TODO
        break;

    case JSC::Yarr::PatternTerm::TypeBackReference:
        throw CVC4RegexCompilerException("Unsupported usage of back references in regex");
        break;

    case JSC::Yarr::PatternTerm::TypeForwardReference:
        throw CVC4RegexCompilerException("Unsupported usage of forward references in regex");
        break;

    case JSC::Yarr::PatternTerm::TypeParenthesesSubpattern:
        // TODO
        break;

    case JSC::Yarr::PatternTerm::TypeParentheticalAssertion:
        // TODO
        break;

    case JSC::Yarr::PatternTerm::TypeDotStarEnclosure:
        // TODO
        break;

    default:
        throw CVC4RegexCompilerException("Unknown pattern term encountered");
    }

    return result.str();
}

std::string CVC4RegexCompiler::compile(const std::string &javaScriptRegex)
{
    bool caseSensitivity = false;
    bool multiline = false;

    const char* m_constructionError = 0;
    JSC::Yarr::YarrPattern pattern(JSC::UString(javaScriptRegex.c_str()), caseSensitivity, multiline, &m_constructionError);

    if (m_constructionError) {
        std::string err = "RegularExpression: YARR compile failed with " + std::string(m_constructionError);
        throw CVC4RegexCompilerException(err);
    }

    return visitPatternDisjunction(pattern.m_body);
}

CVC4RegexCompiler::CVC4RegexCompiler()
{
}
