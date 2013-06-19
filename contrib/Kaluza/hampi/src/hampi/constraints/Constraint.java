/*******************************************************************************
 * The MIT License
 *
 * Copyright (c) 2008 Adam Kiezun
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 ******************************************************************************/
package hampi.constraints;

import java.util.*;

/**
 * Describes a constraint that may involve string variables.<br>
 * NOTE: Constructors of all constraints are package visible to force usage of
 * HampiConstraint facade
 */
public abstract class Constraint{

  private final ElementKind kind;

  Constraint(ElementKind kind){
    this.kind = kind;
  }

  /**
   * Returns the kind of the expression. Useful for implementing enum switches.
   */
  public final ElementKind getKind(){
    return kind;
  }

  @Override
  public abstract String toString();

  @Override
  public abstract int hashCode();

  @Override
  public abstract boolean equals(Object obj);

  /**
   * Returns all conjuncts in this expression. If this expression is a
   * conjuction, then it returns all sub-expressions, otherwise it returns a
   * singleton set.
   */
  public abstract List<RegexpConstraint> getConjuncts();

  /**
   * Returns the set of all free variables mentioned in this constraint.
   */
  public abstract Set<VariableExpression> getVariables();

  /**
   * Implements the visitor pattern.
   */
  public abstract void accept(ConstraintGrammarVisitor visitor);

  /**
   * Returns the Java code that creates this constraint.
   */
  public abstract String toJavaCode(String hampiVar);

  /**
   * Returns the set of characters used in this constraint.
   */
  public final Set<Character> charsUsed(){
    final Set<Character> result = new LinkedHashSet<Character>();
    ConstraintGrammarVisitor v = new ConstraintGrammarVisitor(){
      @Override
      public void visitConst(ConstRegexp c){
        result.addAll(asCharacterList(c.getString()));
      }

      @Override
      public void visitConstantExpression(ConstantExpression c){
        result.addAll(asCharacterList(c.getString()));
      }

      private List<Character> asCharacterList(String s){
        List<Character> list = new ArrayList<Character>(s.length());
        for (char d : s.toCharArray()){
          list.add(d);
        }
        return list;
      }
    };
    this.accept(v);
    return result;
  }

  /**
   * Upper bound on the length of the variable in a satisfying assignment. For
   * regexp, it returns a upper bound of the regexpr and for conjunctions, it's
   * a min of upper bounds for conjuncts.
   */
  public abstract int varLengthUpperBound();

  /**
   * Lower bound on the length of the variable in a satisfying assignment. For
   * regexp, it returns a lower bound of the regexpr. For conjunctions, it
   * returns a max of lower bounds for conjuncts.
   */
  public abstract int varLengthLowerBound();

  /**
   * Returns the set of characters that must appear in every string that
   * satisfies the constraint.
   */
  public abstract Set<Character> alphabetLowerbound();

}
