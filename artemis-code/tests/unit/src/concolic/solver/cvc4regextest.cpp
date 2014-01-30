#include "include/gtest/gtest.h"

#include "concolic/solver/constraintwriter/cvc4regexcompiler.h"

namespace artemis
{

TEST(CVC4RegexTest, EMPTY_STRING) {
    std::string result = CVC4RegexCompiler::compile("");
    ASSERT_EQ("(str.to.re \"\")", result);
}

TEST(CVC4RegexTest, SIMPLE_CHAR) {
    std::string result = CVC4RegexCompiler::compile("c");
    ASSERT_EQ("(str.to.re \"c\")", result);
}

TEST(CVC4RegexTest, SIMPLE_CHAR_X2) {
    std::string result = CVC4RegexCompiler::compile("cc");
    ASSERT_EQ("(re.++ (str.to.re \"c\") (str.to.re \"c\"))", result);
}

TEST(CVC4RegexTest, SIMPLE_CHAR_CHAR) {
    std::string result = CVC4RegexCompiler::compile("ab");
    ASSERT_EQ("(re.++ (str.to.re \"a\") (str.to.re \"b\"))", result);
}

TEST(CVC4RegexTest, DISJ) {
    std::string result = CVC4RegexCompiler::compile("a|b");
    ASSERT_EQ("(re.or (str.to.re \"a\") (str.to.re \"b\"))", result);
}

TEST(CVC4RegexTest, WILDCARD_CHAR) {
    std::string result = CVC4RegexCompiler::compile("c*");
    ASSERT_EQ("(re.* (str.to.re \"c\"))", result);
}

TEST(CVC4RegexTest, PLUS_CHAR) {
    std::string result = CVC4RegexCompiler::compile("c+");
    ASSERT_EQ("(re.++ (str.to.re \"c\") (re.* (str.to.re \"c\")))", result);
}

TEST(CVC4RegexTest, OPTIONAL_CHAR) {
    std::string result = CVC4RegexCompiler::compile("c?");
    ASSERT_EQ("(re.opt (str.to.re \"c\"))", result);
}

TEST(CVC4RegexTest, FIXED_NUMBER_CHAR_0_1) {
    std::string result = CVC4RegexCompiler::compile("c{0,1}");
    ASSERT_EQ("(re.opt (str.to.re \"c\"))", result);
}

TEST(CVC4RegexTest, FIXED_NUMBER_CHAR_0_2) {
    std::string result = CVC4RegexCompiler::compile("c{0,2}");
    ASSERT_EQ("(re.++ (re.opt (str.to.re \"c\")) (re.opt (str.to.re \"c\")))", result);
}

TEST(CVC4RegexTest, FIXED_NUMBER_CHAR_1_2) {
    std::string result = CVC4RegexCompiler::compile("c{1,2}");
    ASSERT_EQ("(re.++ (str.to.re \"c\") (re.opt (str.to.re \"c\")))", result);
}

TEST(CVC4RegexTest, FIXED_NUMBER_CHAR_1_3) {
    std::string result = CVC4RegexCompiler::compile("c{1,3}");
    ASSERT_EQ("(re.++ (str.to.re \"c\") (re.++ (re.opt (str.to.re \"c\")) (re.opt (str.to.re \"c\"))))", result);
}

TEST(CVC4RegexTest, RANGE_A_Z) {
    std::string result = CVC4RegexCompiler::compile("[a-z]");
    ASSERT_EQ("(re.range \"a\" \"z\")", result);
}

TEST(CVC4RegexTest, RANGE_A_B_D_E) {
    std::string result = CVC4RegexCompiler::compile("[a-bd-e]");
    ASSERT_EQ("(re.or (re.range \"a\" \"b\") (re.range \"d\" \"e\"))", result);
}

TEST(CVC4RegexTest, CHAR_ABC) {
    std::string result = CVC4RegexCompiler::compile("[abc]");
    ASSERT_EQ("(re.or \"a\" \"b\" \"c\")", result);
}

TEST(CVC4RegexTest, NESTED_MATCHES) {
    std::string result = CVC4RegexCompiler::compile("a(b)(c)");
    ASSERT_EQ("(re.++ (str.to.re \"a\") (str.to.re \"b\") (str.to.re \"c\"))", result);
}

TEST(CVC4RegexTest, NESTED_MATCHES_WILDCARD) {
    std::string result = CVC4RegexCompiler::compile("a(b|c)*");
    ASSERT_EQ("(re.++ (str.to.re \"a\") (re.* (re.or (str.to.re \"b\") (str.to.re \"c\"))))", result);
}

TEST(CVC4RegexTest, RL_EXAMPLE_1) {
    try {
        std::string result = CVC4RegexCompiler::compile("[a-zA-Z]{3}\\+?");
        ASSERT_EQ("(re.++ (re.++ (re.or (re.range \"A\" \"Z\") (re.range \"a\" \"z\")) (re.or (re.range \"A\" \"Z\") (re.range \"a\" \"z\")) (re.or (re.range \"A\" \"Z\") (re.range \"a\" \"z\"))) (re.opt (str.to.re \"+\")))", result);
    } catch (CVC4RegexCompilerException ex) {
        std::cerr << ex.what() << std::endl;
        throw ex;
    }
}

/*TEST(CVC4RegexTest, DOT_STAR) {
    std::string result = CVC4RegexCompiler::compile(".");
    ASSERT_EQ("DOTSTAR", result);
}*/

//^[a-zA-Z]{3}\+?$

//TEST(CVC4RegexTest, CHAR_CLASS_W) {
//    std::string result = CVC4RegexCompiler::compile("[\\w]");
//    ASSERT_EQ("(re.or \"a\" \"b\" \"c\")", result);
//}


}
