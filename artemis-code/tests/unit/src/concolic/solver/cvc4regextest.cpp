#include "include/gtest/gtest.h"

#include "concolic/solver/constraintwriter/cvc4regexcompiler.h"

namespace artemis
{

TEST(CVC4RegexTest, EMPTY_STRING) {
    bool bol, eol = false;
    std::string result = CVC4RegexCompiler::compile("", bol, eol);
    ASSERT_EQ("(str.to.re \"\")", result);
}

TEST(CVC4RegexTest, SIMPLE_CHAR) {
    bool bol, eol = false;
    std::string result = CVC4RegexCompiler::compile("c", bol, eol);
    ASSERT_EQ("(str.to.re \"c\")", result);
}

TEST(CVC4RegexTest, SIMPLE_CHAR_X2) {
    bool bol, eol = false;
    std::string result = CVC4RegexCompiler::compile("cc", bol, eol);
    ASSERT_EQ("(re.++ (str.to.re \"c\") (str.to.re \"c\"))", result);
}

TEST(CVC4RegexTest, SIMPLE_CHAR_CHAR) {
    bool bol, eol = false;
    std::string result = CVC4RegexCompiler::compile("ab", bol, eol);
    ASSERT_EQ("(re.++ (str.to.re \"a\") (str.to.re \"b\"))", result);
}

TEST(CVC4RegexTest, DISJ) {
    bool bol, eol = false;
    std::string result = CVC4RegexCompiler::compile("a|b", bol, eol);
    ASSERT_EQ("(re.or (str.to.re \"a\") (str.to.re \"b\"))", result);
}

TEST(CVC4RegexTest, WILDCARD_CHAR) {
    bool bol, eol = false;
    std::string result = CVC4RegexCompiler::compile("c*", bol, eol);
    ASSERT_EQ("(re.* (str.to.re \"c\"))", result);
}

TEST(CVC4RegexTest, PLUS_CHAR) {
    bool bol, eol = false;
    std::string result = CVC4RegexCompiler::compile("c+", bol, eol);
    ASSERT_EQ("(re.++ (str.to.re \"c\") (re.* (str.to.re \"c\")))", result);
}

TEST(CVC4RegexTest, OPTIONAL_CHAR) {
    bool bol, eol = false;
    std::string result = CVC4RegexCompiler::compile("c?", bol, eol);
    ASSERT_EQ("(re.opt (str.to.re \"c\"))", result);
}

TEST(CVC4RegexTest, FIXED_NUMBER_CHAR_0_1) {
    bool bol, eol = false;
    std::string result = CVC4RegexCompiler::compile("c{0,1}", bol, eol);
    ASSERT_EQ("(re.opt (str.to.re \"c\"))", result);
}

TEST(CVC4RegexTest, FIXED_NUMBER_CHAR_0_2) {
    bool bol, eol = false;
    std::string result = CVC4RegexCompiler::compile("c{0,2}", bol, eol);
    ASSERT_EQ("(re.++ (re.opt (str.to.re \"c\")) (re.opt (str.to.re \"c\")))", result);
}

TEST(CVC4RegexTest, FIXED_NUMBER_CHAR_1_2) {
    bool bol, eol = false;
    std::string result = CVC4RegexCompiler::compile("c{1,2}", bol, eol);
    ASSERT_EQ("(re.++ (str.to.re \"c\") (re.opt (str.to.re \"c\")))", result);
}

TEST(CVC4RegexTest, FIXED_NUMBER_CHAR_1_3) {
    bool bol, eol = false;
    std::string result = CVC4RegexCompiler::compile("c{1,3}", bol, eol);
    ASSERT_EQ("(re.++ (str.to.re \"c\") (re.++ (re.opt (str.to.re \"c\")) (re.opt (str.to.re \"c\"))))", result);
}

TEST(CVC4RegexTest, RANGE_A_Z) {
    bool bol, eol = false;
    std::string result = CVC4RegexCompiler::compile("[a-z]", bol, eol);
    ASSERT_EQ("(re.range \"a\" \"z\")", result);
}

TEST(CVC4RegexTest, RANGE_A_B_D_E) {
    bool bol, eol = false;
    std::string result = CVC4RegexCompiler::compile("[a-bd-e]", bol, eol);
    ASSERT_EQ("(re.or (re.range \"a\" \"b\") (re.range \"d\" \"e\"))", result);
}

TEST(CVC4RegexTest, CHAR_ABC) {
    bool bol, eol = false;
    std::string result = CVC4RegexCompiler::compile("[abc]", bol, eol);
    ASSERT_EQ("(re.or \"a\" \"b\" \"c\")", result);
}

TEST(CVC4RegexTest, NESTED_MATCHES) {
    bool bol, eol = false;
    std::string result = CVC4RegexCompiler::compile("a(b)(c)", bol, eol);
    ASSERT_EQ("(re.++ (str.to.re \"a\") (str.to.re \"b\") (str.to.re \"c\"))", result);
}

TEST(CVC4RegexTest, NESTED_MATCHES_WILDCARD) {
    bool bol, eol = false;
    std::string result = CVC4RegexCompiler::compile("a(b|c)*", bol, eol);
    ASSERT_EQ("(re.++ (str.to.re \"a\") (re.* (re.or (str.to.re \"b\") (str.to.re \"c\"))))", result);
}

TEST(CVC4RegexTest, RL_EXAMPLE_1) {
    try {
        bool bol, eol = false;
        std::string result = CVC4RegexCompiler::compile("[a-zA-Z]{3}\\+?", bol, eol);
        ASSERT_EQ("(re.++ (re.++ (re.or (re.range \"A\" \"Z\") (re.range \"a\" \"z\")) (re.or (re.range \"A\" \"Z\") (re.range \"a\" \"z\")) (re.or (re.range \"A\" \"Z\") (re.range \"a\" \"z\"))) (re.opt (str.to.re \"+\")))", result);
    } catch (CVC4RegexCompilerException ex) {
        std::cerr << ex.what() << std::endl;
        throw ex;
    }
}

TEST(CVC4RegexTest, EOL_BOL_LEGACY_TEST) {
    bool bol, eol = false;
    std::string result = CVC4RegexCompiler::compile("^a$", bol, eol);
    ASSERT_EQ("(str.to.re \"a\")", result);
    ASSERT_EQ(bol, true);
    ASSERT_EQ(eol, true);
}

TEST(CVC4RegexTest, DOT_STAR) {
    bool bol, eol = false;
    std::string result = CVC4RegexCompiler::compile(".", bol, eol);
    ASSERT_EQ("(re.or (re.range \"0\" \"9\") (re.range \"A\" \"Z\") (re.range \"a\" \"z\") \"_\" \"-\")", result);
}

TEST(CVC4RegexTest, CHAR_CLASS_W) {
    bool bol, eol = false;
    std::string result = CVC4RegexCompiler::compile("\\w", bol, eol);
    ASSERT_EQ("(re.or (re.range \"0\" \"9\") (re.range \"A\" \"Z\") (re.range \"a\" \"z\") \"_\")", result);
}


}
