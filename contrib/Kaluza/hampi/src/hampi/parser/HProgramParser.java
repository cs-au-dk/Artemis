package hampi.parser;

import hampi.HampiException;

import java.io.*;
import java.util.*;

import org.antlr.runtime.*;
import org.antlr.runtime.tree.*;

/**
 * The main parser and well-formedness checker.
 */
public final class HProgramParser{

  /**
   * Parses the file given by the path and returns the AST.
   */
  public static HProgram parse(String filePath) throws RecognitionException,IOException{
    return parse(filePath, System.out);
  }

  /**
   * Parses the string and returns the AST.
   */
  public static HProgram parseString(String string) throws RecognitionException,IOException{
    //NOTE: it's OK not to close ByteArrayInputStreams
    return parse(System.out, new ByteArrayInputStream(string.getBytes()));
  }

  /**
   * Parses the file given by the path and returns the AST. Outputs the errors
   * to the provided stream. If there are errors, returns null. Does not close
   * the stream.
   */
  public static HProgram parse(String filePath, OutputStream os) throws RecognitionException,IOException{
    return parse(os, new FileInputStream(filePath));
  }

  /**
   * Parses the given input and returns the AST. Outputs the errors to the
   * provided stream. If there are errors, returns null. Does not close the
   * streams.
   */
  public static HProgram parse(OutputStream os, InputStream is) throws IOException,RecognitionException{
    //Note: The parser prints stuff to stderr so we divert it to stdout (otherwise the streams get scrambled)
    PrintStream oldErr = System.err;
    PrintStream myErrorStream = new PrintStream(os);
    System.setErr(myErrorStream);
    try{
      HampiLexer lexer = new HampiLexer(new ANTLRInputStream(is));
      HampiParser parser = new HampiParser(new CommonTokenStream(lexer));
      CommonTree ast = (CommonTree) parser.program().getTree();
      CommonTreeNodeStream nodes = new CommonTreeNodeStream(ast);
      int numberOfSyntaxErrors = parser.getNumberOfSyntaxErrors();
      if (numberOfSyntaxErrors != 0)
        return null;
      HampiTree walker = new HampiTree(nodes);
      return walker.program();
    }finally{
      System.setErr(oldErr);
    }
  }

  /**
   * Checks the well-formedness of the hampi constraint. Rules:<br>
   * exactly one variable<br>
   * at least one assert<br>
   * all names are defined (may be defined before they are used, e.g. cfg
   * requires this).<br>
   * all names are defined exactly once.<br>
   * //no left recursion (direct or indirect) in cfg (NOTE: is this necessary?)<br>
   * regexps are well-formed<br>
   * fix operator uses a cfg var and size > 0<br>
   * assert: in operator uses reg var<br>
   * 
   * This method returns an error message if the check fails or null of there is
   * no problem.
   */
  public static String checkWellFormedness(HProgram prog){
    try{
      checkExactlyOneVariable(prog);
      checkAtLeastOneAssert(prog);
      HTypeEnvironment tenv = getTypeEnvironment(prog);
      prog.typeCheck(tenv);
      return null;
    }catch (HampiException e){
      return e.getMessage();
    }
  }

  public static class HTypeEnvironment{
    private final Map<String, HType> types;

    public HTypeEnvironment(){
      types = new LinkedHashMap<String, HType>();
    }

    /**
     * Sets the new type, returns the old type or null if there was no old type.
     */
    public HType add(String name, HType type){
      return types.put(name, type);
    }

    public HType getType(String varname){
      return types.get(varname);
    }

    public Set<String> getVarNames(){
      return types.keySet();
    }

    @Override
    public String toString(){
      return types.toString();
    }
  }

  /**
   * Creates a mapping from variable names to types.
   */
  private static HTypeEnvironment getTypeEnvironment(HProgram prog){
    HTypeEnvironment tenv = new HTypeEnvironment();
    for (HStatement stmt : prog.getStatements()){
      if (stmt instanceof HVarDeclStatement){
        HVarDeclStatement s = (HVarDeclStatement) stmt;
        HType oldType = tenv.add(s.getVarName(), HType.STRING_TYPE);
        if (oldType != null)
          throw new HampiException("multiply defined variable " + s.getVarName());
      }
      if (stmt instanceof CFGStatement){
        CFGStatement s = (CFGStatement) stmt;
        HType oldType = tenv.add(s.getVarName(), HType.CFG_TYPE);
        if (oldType != null)
          throw new HampiException("multiply defined variable " + s.getVarName());
      }
      if (stmt instanceof HRegDeclStatement){
        HRegDeclStatement s = (HRegDeclStatement) stmt;
        HType oldType = tenv.add(s.getVarName(), HType.REG_TYPE);
        if (oldType != null)
          throw new HampiException("multiply defined variable " + s.getVarName());
      }
      if (stmt instanceof HValDeclStatement){
        HValDeclStatement s = (HValDeclStatement) stmt;
        HType oldType = tenv.add(s.getVarName(), s.getExpression().getType(tenv));
        if (oldType != null)
          throw new HampiException("multiply defined variable " + s.getVarName());
      }
    }
    return tenv;
  }

  /**
   * Checks that prog contains at least one assert statement.
   */
  private static void checkAtLeastOneAssert(HProgram prog){
    for (HStatement statement : prog.getStatements()){
      if (statement instanceof HAssertStatement)
        return;
    }
    throw new HampiException("at least one assert expected ");
  }

  /**
   * Checks that prog contains exactly one string variable.
   */
  private static void checkExactlyOneVariable(HProgram prog){
    String varName = null;
    for (HStatement statement : prog.getStatements()){
      String name = (statement instanceof HVarDeclStatement) ? ((HVarDeclStatement) statement).getVarName() : null;
      if (varName != null && name != null)
        throw new HampiException("more than one string variable declared " + varName + " " + name);
      if (varName == null){
        varName = name;
      }
    }
    if (varName == null)
      throw new HampiException("no string variable declared");
  }
}
