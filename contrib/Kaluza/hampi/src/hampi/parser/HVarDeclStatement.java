package hampi.parser;

import hampi.parser.HProgramParser.HTypeEnvironment;

public final class HVarDeclStatement extends HStatement{

  private final String name;
  private final int    size;

  public HVarDeclStatement(String text, String size){
    super(HGrammarElementKind.STMT_VARDECL);
    this.name = text;
    this.size = Integer.parseInt(size);
  }

  @Override
  public String unparse(){
    return "var " + name + ":" + size + ";";
  }

  /**
   * Returns the variable's name.
   */
  public String getVarName(){
    return name;
  }

  /**
   * Returns the declared size of the variable.
   */
  public int getSize(){
    return size;
  }

  @Override
  public void typeCheck(HTypeEnvironment tenv){
    //nothing
  }

  @Override
  public void accept(HGrammarVisitor v){
    v.visitVarDeclStatement(this);
  }
}
