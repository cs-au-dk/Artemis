package hampi.parser;

import hampi.parser.HProgramParser.HTypeEnvironment;

public final class HAssertStatement extends HStatement{

  private final HBooleanExpression b;

  public HAssertStatement(HBooleanExpression b){
    super(HGrammarElementKind.STMT_ASSERT);
    this.b = b;
  }

  /**
   * Returns the boolean expression to assert.
   */
  public HBooleanExpression getBooleanExpression(){
    return b;
  }

  @Override
  public String unparse(){
    return "assert " + b.toString() + ";";
  }

  @Override
  public void typeCheck(HTypeEnvironment tenv){
    b.typeCheck(tenv);
  }

  @Override
  public void accept(HGrammarVisitor v){
    v.visitAssertStatement(this);
    b.accept(v);
  }
}
