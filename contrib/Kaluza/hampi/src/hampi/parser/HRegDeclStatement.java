package hampi.parser;

import hampi.parser.HProgramParser.HTypeEnvironment;

public final class HRegDeclStatement extends HStatement{

  private final String        id;
  private final HRegDefinition reg;

  public HRegDeclStatement(String string, HRegDefinition r){
    super(HGrammarElementKind.STMT_REGDECL);
    assert string != null;
    assert r != null;
    this.id = string;
    this.reg = r;
  }

  public HRegDefinition getRegexp(){
    return reg;
  }

  @Override
  public String unparse(){
    return "reg " + id + " := " + reg.toString() + ";";
  }

  public String getVarName(){
    return id;
  }

  @Override
  public void typeCheck(HTypeEnvironment tenv){
    reg.typeCheck(tenv);
  }

  @Override
  public void accept(HGrammarVisitor v){
    v.visitRegDeclStatement(this);
    reg.accept(v);
  }
}
