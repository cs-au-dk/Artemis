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

import hampi.Solution;

import java.util.*;

/**
 * Represents a concatenation expression.
 */
public final class ConcatExpression extends Expression{

  private final List<Expression> subexpressions;

  ConcatExpression(Expression... expressions){
    this(Arrays.asList(expressions));
  }

  ConcatExpression(List<Expression> expressions){
    super(ElementKind.CONCAT_EXPRESSION);
    this.subexpressions = expressions;
  }

  public List<Expression> getSubexpressions(){
    return subexpressions;
  }

  @Override
  public boolean equals(Object obj){
    if (!(obj instanceof ConcatExpression))
      return false;
    ConcatExpression that = (ConcatExpression) obj;
    return that.subexpressions.equals(this.subexpressions);
  }

  @Override
  public int hashCode(){
    return subexpressions.hashCode();
  }

  @Override
  public String toString(){
    StringBuilder b = new StringBuilder();
    for (int i = 0; i < subexpressions.size(); i++){
      if (i != 0){
        b.append(" . ");
      }
      b.append(subexpressions.get(i).toString());
    }
    return b.toString();
  }

  @Override
  public Set<VariableExpression> getVariables(){
    Set<VariableExpression> result = new LinkedHashSet<VariableExpression>();
    for (Expression expression : subexpressions){
      result.addAll(expression.getVariables());
    }
    return result;
  }

  @Override
  public void accept(ConstraintGrammarVisitor visitor){
    for (Expression e : subexpressions){
      e.accept(visitor);
    }
    visitor.visitConcatExpression(this);
  }

  @Override
  public String getValue(Solution solution){
    StringBuilder b = new StringBuilder();
    for (Expression sub : subexpressions){
      b.append(sub.getValue(solution));
    }
    return b.toString();
  }

  @Override
  public String toJavaCode(String hampiVar){
    StringBuilder b = new StringBuilder();
    b.append(hampiVar + ".concatExpr(");
    for (int i = 0; i < subexpressions.size(); i++){
      if (i != 0){
        b.append(", ");
      }
      b.append(subexpressions.get(i).toJavaCode(hampiVar));
    }
    b.append(")");
    return b.toString();
  }

  @Override
  public int getSizeLowerBound(){
    int sum = 0;
    for (Expression e : subexpressions){
      int low = e.getSizeLowerBound();
      if (low == Integer.MAX_VALUE)
        return low; //not going to get any larger so just return
      else{
        sum += low;
      }
    }
    return sum;
  }

  @Override
  public int getSizeUpperBound(){
    int sum = 0;
    for (Expression e : subexpressions){
      int high = e.getSizeUpperBound();
      if (high == Integer.MAX_VALUE)
        return high;//not going to get any larger so just return
      else{
        sum += high;
      }
    }
    return sum;
  }
}
