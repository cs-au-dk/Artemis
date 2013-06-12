package hampi.stp;

import static java.lang.Math.*;
import hampi.*;
import hampi.constraints.*;
import hampi.utils.*;

import java.util.*;

import stp.*;

/**
 * A string solver implemented using the STP prover.
 */
public class STPSolver extends AbstractSolver{

  /**
   * Flag to control the 'split-top-level-ors' optimization.
   */
  private static final boolean OPT_TOP_DISJ_SPLIT = true;

  /**
   * If true, Hampi calls STP separately for each conjuction, otherwise Hampi
   * puts all conjunctions in 1 STP formula with disjunction.
   * XXX this is not fully implemented yet.
   */
  public static final boolean INCREMENTAL = false;

  public final StopWatch shiftingTimer = new StopWatch("shifting");
  private final StopWatch distroTimer = new StopWatch("distro");
  private final StopWatch nativeEncodingTimer = new StopWatch("native encoding");
  private final StopWatch solvingTimer = new StopWatch("native STP solving");
  private final StopWatch createTimer = new StopWatch("create STP formula");
  public final StopWatch nativeSTPObjectCreationTimer = new StopWatch("create STP native objects creation");

  private CharacterEncoding encoding;
  private final STPSolverCache cache;
  private final STPExpr TRUE = new BoolConstSTPExpr(this, true);
  private final STPExpr FALSE = new BoolConstSTPExpr(this, false);

  private final PigeonHoleDistributor distributor;

  public STPSolver(){
    super("STP-regexp");
    cache = new STPSolverCache();
    distributor = new PigeonHoleDistributor();
  }

  @Override
  public Solution solve(Constraint c, int size){
    try{
      if (verbose){
        System.out.println();
        System.out.println("size:" + size);
        //                System.out.println(c);
      }
      if (c.getConjuncts().isEmpty()){
        System.err.println("ASSERT(TRUE);\n");
    	  return Solution.createSAT();
      }

      Solution simpleSolution = trySimpleCases(c);
      if (simpleSolution != null){
       System.err.println("ASSERT(FALSE);\n");
    	 return simpleSolution;
      }

      if (c.getVariables().size() != 1)
        throw new UnsupportedOperationException("multi-variable constraints are not supported yet");

      int min = c.varLengthLowerBound();

      if (size < min){
        System.err.println("ASSERT(FALSE);\n");
        return Solution.createUNSAT(); //cut this short
      }
      VariableExpression v = c.getVariables().iterator().next();
      if (size == 0 && min == 0){//try empty string without calling STP
    	//ignoring as empty string can't happen in our case -- solveLength will remove it -- devdatta
    	Solution emptyStringSol = Solution.createSAT();
        emptyStringSol.setValue(v, "");
        boolean checkSolution = new SolutionChecker().checkSolution(c, emptyStringSol);
        if (checkSolution)
          return emptyStringSol;
        else{
          min = 1;
        }
      }

      int upperBound = c.varLengthUpperBound();

      if (upperBound < min){
    	  System.err.println("ASSERT(FALSE);\n");
    	  return Solution.createUNSAT(); //cut this short
      }
      int varlength = size;
      if (verbose){
        System.out.println("length:" + varlength);
      }
      createTimer.start();

      encoding = new CharacterEncoding();

      List<STPExpr> expressions = new ArrayList<STPExpr>(c.getConjuncts().size());

      BVExpr[] bvs = new BVExpr[c.getConjuncts().size()];
      int[] bvLens = new int[c.getConjuncts().size()];
      int count = 0;
      for (RegexpConstraint conjunct : c.getConjuncts()){
        RegexpConstraint rc = conjunct;
        int bvLength = getBVLength(varlength, rc);

        BVExpr bv = BVExpr.create(this, "bv" + count, encodingSize() * bvLength);
        bvs[count] = bv;
        bvLens[count] = bvLength;
        count++;
//        System.err.println(bv.toSTPString(0)+";");

        STPExpr e = createRegexpConstraint(bv, rc, bvLength, varlength);
        System.err.print("ASSERT(");
	e.toSTPString(0);
	System.err.println(");");

        expressions.add(e);
        if (e.equals(falseExpr()))
          return Solution.createUNSAT();
      }
      //Do I need to write this line down ?
      System.exit(0);
      STPExpr stpFormula = AndExpr.create(this, expressions);
      STPExpr fullFormula = AndExpr.create(this, stpFormula, linkVars(c.getConjuncts(), bvs, bvLens, varlength));


      createTimer.stop();
      List<STPExpr> alternatives;
      if (OPT_TOP_DISJ_SPLIT && fullFormula.getKind() == STPExprKind.OrExpr){
        List<STPExpr> subexpressions = ((OrExpr) fullFormula).getSubexpressions();
        alternatives = subexpressions;
      }else{
        alternatives = Collections.singletonList(fullFormula);
      }
      if (INCREMENTAL){
        alternatives = Arrays.asList(OrExpr.create(this, alternatives));//all alternatives together
      }

      for (STPExpr expr : alternatives){
        SolvingContext sc;
        if (INCREMENTAL){
          sc=new SolvingContext(ChoiceGenerator.<STPExpr>createOneByOne(), encoding);//XXX does not work yet
        }else{
          sc = new SolvingContext(ChoiceGenerator.<STPExpr>createFull(), encoding);
        }
        while (!sc.getChoiceGenerator().isDone()){//TODO replace the 'alternatives' loop with this loop
          VC vc = new VC();
          VC.setFlags('a');//turn off optimizations - it makes it faster because our constraints are simple
          sc.setVC(vc);
          nativeEncodingTimer.start();
          Expr full = expr.getExpr(sc, 0);
          nativeEncodingTimer.stop();
          solvingTimer.start();
          vc.assertFormula(full);


          //System.out.println(full.exprString());
          int query = vc.query(falseExpr().getExpr(sc, 0));
          solvingTimer.stop();
          //          System.out.println("Solving STP " + (query == 0) + "\n------------------------");
          if (query == 0){
            Solution sat = Solution.createSAT();
            String decodedValue = decodeValue(sc, c.getConjuncts(), bvs, varlength);
            if (decodedValue != null){
              sat.setValue(v, decodedValue);
            }
            vc.Destroy();
            return sat;
          }
          sc.getChoiceGenerator().reset();
          vc.Destroy();
        }
            }

      return Solution.createUNSAT();
    }finally{
      if (verbose){
        System.out.println(createTimer);
        System.out.println(distroTimer);
        System.out.println(shiftingTimer);
        //                System.out.println(shiftingTimer.getTimesHistogram().toStringSortedByKey());
        System.out.println(nativeEncodingTimer);
        System.out.println(nativeSTPObjectCreationTimer);
        System.out.println(solvingTimer);
      }
    }
  }

  /**
   * Returns the size of bitvector (in chars) given the size of var (in chars)
   */
  private int getBVLength(int varlength, RegexpConstraint c){
    Set<VariableExpression> vars = c.getVariables();
    if (vars.isEmpty())
      return c.getExpression().getSizeLowerBound();
    Solution s = Solution.createSAT();
    String val = Utils.repeat(varlength, 'a');
    s.setValue(vars.iterator().next(), val);
    return c.getExpression().getValue(s).length();
  }

  /**
   * Returns the solved value for the variable, or null if there is no variable
   * at all.
   */
  private String decodeValue(SolvingContext sc, List<RegexpConstraint> conjuncts, BVExpr[] bvs, int varLen){
    for (int i = 0; i < bvs.length; i++){
      RegexpConstraint c = conjuncts.get(i);
      if (!c.getVariables().isEmpty()){
        String fullBVDecoded = encoding.decodeValue(sc.getVC(), bvs[i].getExpr(sc, 0));
        List<Integer> varOffsets = varOffset(c, varLen, varLen);
        int varOffset = varOffsets.get(0);//just take the first
        return fullBVDecoded.substring(varOffset, varOffset + varLen);
      }
    }
    return null;
  }

  /**
   * Returns the offset and length of the variable (in terms of chars).
   *
   */
  private List<Integer> varOffset(RegexpConstraint c, int bvLen, int varLen){
    List<Integer> offsets = new ArrayList<Integer>();
    Expression expr = c.getExpression();
    if (expr.getKind() == ElementKind.CONCAT_EXPRESSION){
      ConcatExpression ce = (ConcatExpression) expr;
      List<Expression> subs = ce.getSubexpressions();
      int constLen = 0;
      for (Expression sub : subs){
        if (sub.getKind() == ElementKind.CONST_EXPRESSION){
          ConstantExpression constExpr = (ConstantExpression) sub;
          String str = constExpr.getString();
          constLen += str.length();
        }
        if (sub.getKind() == ElementKind.VAR_EXPRESSION){
          offsets.add(constLen);
          constLen += varLen;
        }
        if (sub.getKind() == ElementKind.CONCAT_EXPRESSION)
          throw new IllegalArgumentException("should not have nested concats: " + c);
      }
    }else if (expr.getKind() == ElementKind.VAR_EXPRESSION){
      offsets.add(0);
    }else
      throw new IllegalStateException("unexpected constraint " + c);
    return offsets;
  }

  /**
   * Creates an expression that means: the parts of bitvectors that denote the
   * variable are all equal.
   */
  private STPExpr linkVars(List<RegexpConstraint> conjuncts, BVExpr[] bvs, int bvLens[], int varLen){
    if (bvs.length == 0)
      return trueExpr();
    List<STPExpr> expressions = new ArrayList<STPExpr>(conjuncts.size());
    for (int i = 0; i < conjuncts.size(); i++){
      RegexpConstraint c = conjuncts.get(i);

      List<Integer> varOffsets = varOffset(c, bvLens[i], varLen);
      for (int varOffset : varOffsets){
        int enc = encodingSize();
        STPExpr encoded = bvs[i].extract(enc * (varOffset + varLen) - 1, enc * varOffset, enc);
        expressions.add(encoded);
      }
    }
    return allEqual(expressions);
  }

  /**
   * Returns the number of bits per character in the encoding.
   */
  private int encodingSize(){
    return encoding.size();
  }

  /**
   * Create and expression that equates all subexpressions.
   */
  private STPExpr allEqual(List<STPExpr> expressions){
    if (expressions.size() < 2)
      return trueExpr();
    STPExpr result = trueExpr();
    STPExpr first = expressions.get(0);
    for (STPExpr e : expressions){
      if (e != first){//skip comparing first to self
        STPExpr prevEqCurr = first.binOp(BinOpKind.EQ_OP, e);
        result = AndExpr.create(this, result, prevEqCurr);
      }
    }
    return result;
  }

  //bvlen is in in chars (not bits)
  //varlen is in in chars (not bits)
  private STPExpr createRegexpConstraint(BVExpr bv, RegexpConstraint rc, int bvLen, int varLen){
    Regexp regexp = rc.getRegexp();

    //    System.out.println("regexp:" + regexp);
    StopWatch stpAcceptTimer = new StopWatch("STP accept ");
    stpAcceptTimer.start();
    STPExpr tryLength = stpAccept(0, bvLen, regexp, bv);
    stpAcceptTimer.stop();

    //fixing the constant prefix and suffix
    Expression expr = rc.getExpression();
    if (expr.getKind() == ElementKind.VAR_EXPRESSION)
      return rc.isMembership() ? tryLength : NotExpr.create(tryLength, this);
    if (expr.getKind() == ElementKind.CONCAT_EXPRESSION){
      if (tryLength.equals(falseExpr()) && rc.isMembership())
        return falseExpr();

      ConcatExpression ce = (ConcatExpression) expr;
      List<Expression> subs = ce.getSubexpressions();
      STPExpr result = tryLength;
      int offsetSoFar = 0;
      for (Expression sub : subs){
        if (sub.getKind() == ElementKind.CONST_EXPRESSION){
          ConstantExpression constExpr = (ConstantExpression) sub;
          String str = constExpr.getString();
          //TODO encode as a single equals not a conjunction char-by-char
          for (int i = 0; i < str.length(); i++){
            int num = encoding.encodedValue(str.charAt(i));
            STPExpr ch = encoding.extractedChar(i + offsetSoFar, bv);
            result = AndExpr.create(this, result, ch.binOp(BinOpKind.EQ_OP, ConstExpr.create(this, num)));
          }
          offsetSoFar += str.length();
        }
        if (sub.getKind() == ElementKind.VAR_EXPRESSION){
          offsetSoFar += varLen;
        }
        if (sub.getKind() == ElementKind.CONCAT_EXPRESSION)
          throw new IllegalArgumentException("should not have nested concats: " + rc);
      }
      return rc.isMembership() ? result : NotExpr.create(result, this);
    }
    throw new UnsupportedOperationException("not implemented yet " + rc);
  }

  /**
   * Create expression that says: suffix of bv starting at startIdx is in
   * L(regexp).
   */
  private STPExpr stpAccept(int startIdx, int varLen, Regexp regexp, BVExpr bv){
    //    System.out.println("stpAccept:" + regexp + " " + startIdx + " " + varLen);
    if (regexp.getKind() == ElementKind.CONST_REGEXP)
      return constant(startIdx, varLen, (ConstRegexp) regexp, bv);
    else if (regexp.getKind() == ElementKind.CONCAT_REGEXP)
      return concat(startIdx, varLen, (ConcatRegexp) regexp, bv);
    else if (regexp.getKind() == ElementKind.OR_REGEXP)
      return or(startIdx, varLen, (OrRegexp) regexp, bv);
    else if (regexp.getKind() == ElementKind.STAR_REGEXP)
      return star(startIdx, varLen, (StarRegexp) regexp, bv);
    else
      throw new UnsupportedOperationException("invalid regexp:" + regexp);
  }

  /**
   * Create a STP expression for constant regexp.
   */
  private STPExpr constant(int startIdx, int varLen, ConstRegexp regexp, BVExpr bv){
    //can't be a string of a different size than defined
    String string = regexp.getString();
    if (varLen != string.length())
      return falseExpr();
    if (varLen == 0 && string.isEmpty())
      return trueExpr();
    //TODO can we encode the whole thing as a single equals?
    STPExpr[] letters = new STPExpr[varLen];
    char[] chars = string.toCharArray();
    for (int i = 0; i < varLen; i++){
      STPExpr ch = encoding.extractedChar(i + startIdx, bv);
      int num = encoding.encodedValue(chars[i]);
      STPExpr oneLetter = ch.binOp(BinOpKind.EQ_OP, ConstExpr.create(this, num));
      letters[i] = oneLetter;
    }
    if (letters.length == 1)
      return letters[0];
    else
      return AndExpr.create(this, letters);//call directly, because there will be no shortcuts here for sure
  }

  /**
   * STP expression for Or regexp.
   */
  private STPExpr or(int startIdx, int varLen, OrRegexp regexp, BVExpr bv){
    List<Pair<Character, Character>> ranges = regexp.getCharacterRanges();
    if (ranges != null){
      STPExpr[] rangeExprs = new STPExpr[ranges.size()];
      for (int i = 0; i < ranges.size(); i++){
        Pair<Character, Character> range = ranges.get(i);
        STPExpr ch = encoding.extractedChar(startIdx, bv);
        int low = encoding.encodedValue(range.first);
        int high = encoding.encodedValue(range.second);
        assert (low <= high) : low + " " + high + " " + range.first + " " + range.second;
        if (low == high){
          rangeExprs[i] = ch.binOp(BinOpKind.EQ_OP, ConstExpr.create(this, low));
        }else{
          STPExpr lowBound = ch.binOp(BinOpKind.GE_OP, ConstExpr.create(this, low));
          STPExpr highBound = ch.binOp(BinOpKind.LE_OP, ConstExpr.create(this, high));
          rangeExprs[i] = AndExpr.create(this, lowBound, highBound);
        }
      }
      return OrExpr.create(this, rangeExprs);
    }else{
      List<STPExpr> subexpr = new ArrayList<STPExpr>(regexp.getExpressions().length);
      for (Regexp expr : regexp.getExpressions()){
        STPExpr sub = stpAccept(startIdx, varLen, expr, bv);
        if (sub.equals(trueExpr()))
          return trueExpr();
        subexpr.add(sub);
      }
      return OrExpr.create(this, subexpr);
    }
  }

  /**
   * STP expression for concat regexp.
   */
  private STPExpr concat(int startIdx, int varLen, ConcatRegexp regexp, BVExpr bv){
    STPExpr cached = checkConcatCache(startIdx, varLen, regexp, bv);
    if (cached != null)
      return cached;

    Regexp[] subexpresions = regexp.getExpressions();
    List<Integer> uppers = getUpperBounds(subexpresions);
    List<Integer> lowers = getLowerBounds(subexpresions);

    int holes = subexpresions.length;
    int pigeons = varLen;
    distroTimer.start();
    Set<List<Integer>> distros = distributor.distribute2(holes, pigeons, lowers, uppers);
    distroTimer.stop();

    List<STPExpr> subexpr = new ArrayList<STPExpr>(distros.size());
    for (List<Integer> distro : distros){
      List<STPExpr> parts = new ArrayList<STPExpr>(distro.size());
      int sum = 0;
      for (int i = 0, n = distro.size(); i < n; i++){
        int partSize = distro.get(i);
        STPExpr partExpr = stpAccept(startIdx + sum, partSize, subexpresions[i], bv);
        parts.add(partExpr);
        if (partExpr.equals(falseExpr())){//the whole AND will be a false
          break;
        }
        sum += partSize;
      }
      STPExpr and = AndExpr.create(this, parts);
      if (and.equals(trueExpr()))//the whole OR is a true
        return trueExpr();
      subexpr.add(and);
    }
    STPExpr res = OrExpr.create(this, subexpr);
    addToConcatCache(startIdx, varLen, regexp, res, bv);
    return res;
  }

  private STPExpr checkConcatCache(int startIdx, int varLen, ConcatRegexp regexp, BVExpr bv){
    Pair<Integer, STPExpr> cached = cache.getConcat(varLen, regexp);
    if (cached == null)
      return null;

    //need to shift the expression (we have it cached but for a different start index, so we need to shift)
    int cachedStartIdx = cached.first;
    int diff = startIdx - cachedStartIdx;

    if (diff == 0)
      return cached.second;

    STPExpr shifted = ShiftedSTPExpr.shift(cached.second, diff);
    addToConcatCache(startIdx, varLen, regexp, shifted, bv);
    return shifted;
  }

  private void addToConcatCache(int startIdx, int varLen, ConcatRegexp regexp, STPExpr res, BVExpr bv){
    cache.putConcat(varLen, regexp, Pair.create(startIdx, res));
  }

  /**
   * Returns the list of lower bounds for the expressions.
   */
  private static List<Integer> getLowerBounds(Regexp[] subexpresions){
    List<Integer> result = new ArrayList<Integer>(subexpresions.length);
    for (Regexp subexpresion : subexpresions){
      result.add(subexpresion.getSizeLowerBound());
    }
    return result;
  }

  /**
   * Returns the list of upper bounds for the expressions.
   */
  private static List<Integer> getUpperBounds(Regexp[] subexpresions){
    List<Integer> result = new ArrayList<Integer>(subexpresions.length);
    for (Regexp subexpresion : subexpresions){
      result.add(subexpresion.getSizeUpperBound());
    }
    return result;
  }

  /**
   * STP expression for star regexp.
   */
  private STPExpr star(int startIdx, int varLen, StarRegexp regexp, BVExpr bv){
    if (varLen == 0)
      return trueExpr();
    Regexp expr = regexp.getExpression();
    int exprLowerBound = max(1, expr.getSizeLowerBound());
    int exprUpperBound = min(varLen, expr.getSizeUpperBound());
    int maxNumberOfRepeats = (varLen / exprLowerBound);
    if (maxNumberOfRepeats == 0)
      return falseExpr();
    int minNumberOfRepeats = (varLen / exprUpperBound);
    if (minNumberOfRepeats == 0)
      return trueExpr();
    int pigeons = varLen;
    List<STPExpr> subexpr = new ArrayList<STPExpr>();
    for (int repeats = minNumberOfRepeats; repeats <= maxNumberOfRepeats; repeats++){
      int holes = repeats;

      List<Integer> lowers = repeat(exprLowerBound, repeats);
      List<Integer> uppers = repeat(exprUpperBound, repeats);
      distroTimer.start();
      Set<List<Integer>> distros = distributor.distribute2(holes, pigeons, lowers, uppers);
      distroTimer.stop();
      for (List<Integer> distro : distros){
        List<STPExpr> parts = new ArrayList<STPExpr>(distro.size());
        int sum = 0;
        for (int i = 0; i < distro.size(); i++){
          int partSize = distro.get(i);
          STPExpr partExpr = stpAccept(startIdx + sum, partSize, expr, bv);
          parts.add(partExpr);
          if (partExpr.equals(falseExpr())){
            break;
          }
          sum += partSize;
        }
        STPExpr and = AndExpr.create(this, parts);
        if (and.equals(trueExpr()))//the whole OR is a true
          return trueExpr();
        subexpr.add(and);
      }
    }
    return OrExpr.create(this, subexpr);
  }

  /**
   * List of n repeats of number k.
   */
  private static List<Integer> repeat(int k, int n){
    Integer kInt = k;//box once to save some time
    List<Integer> res = new ArrayList<Integer>(n);
    for (int i = 0; i < n; i++){
      res.add(kInt);
    }
    return res;
  }

  public STPExpr trueExpr(){
    return TRUE;
  }

  public STPExpr falseExpr(){
    return FALSE;
  }

  STPSolverCache getCache(){
    return cache;
  }
}
