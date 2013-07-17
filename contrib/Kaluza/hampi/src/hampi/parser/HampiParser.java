// $ANTLR 3.1b1 src/hampi/parser/Hampi.g 2009-01-17 21:59:26
 
     package hampi.parser; 
   

import org.antlr.runtime.*;
import org.antlr.runtime.tree.*;

public class HampiParser extends Parser {
    public static final String[] tokenNames = new String[] {
        "<invalid>", "<EOR>", "<DOWN>", "<UP>", "CFGPROD", "ASSIGN", "PROGRAM", "CFGOPTION", "CFGSTAR", "CFGPLUS", "FIX", "CONTAINS", "IN", "ASSERT", "CONCAT", "VAR", "CFG", "REG", "VAL", "CONST", "RANGE", "CHARSEQRANGE", "OR", "NOTIN", "NOTCONTAINS", "CFGCHARRANGE", "CFGCHARSEQRANGE", "CFGPRODELEMSET", "VALS", "SEMI", "KW_VAR", "ID", "COLON", "INT", "KW_CFG", "BAR", "LPAREN", "RPAREN", "QUESTION", "STAR", "PLUS", "LSQUARE", "CHAR_LIT", "MINUS", "RSQUARE", "CHAR_SEQ", "STR_LIT", "KW_REG", "KW_FIX", "COMMA", "KW_STAR", "KW_OR", "KW_CONCAT", "KW_VAL", "KW_ASSERT", "KW_IN", "KW_CONTAINS", "KW_NOT", "KW_QUERY", "EQUALS", "EscapeSequence", "NEWLINE", "WS", "COMMENT", "LINE_COMMENT"
    };
    public static final int CFGSTAR=8;
    public static final int FIX=10;
    public static final int STAR=39;
    public static final int KW_VAL=53;
    public static final int LSQUARE=41;
    public static final int CONST=19;
    public static final int CFGPROD=4;
    public static final int CONTAINS=11;
    public static final int EQUALS=59;
    public static final int ID=31;
    public static final int CFG=16;
    public static final int EOF=-1;
    public static final int LPAREN=36;
    public static final int KW_VAR=30;
    public static final int VALS=28;
    public static final int CHAR_SEQ=45;
    public static final int RPAREN=37;
    public static final int IN=12;
    public static final int CFGOPTION=7;
    public static final int COMMA=49;
    public static final int CFGPRODELEMSET=27;
    public static final int CFGCHARRANGE=25;
    public static final int KW_IN=55;
    public static final int VAL=18;
    public static final int PLUS=40;
    public static final int VAR=15;
    public static final int COMMENT=63;
    public static final int NOTCONTAINS=24;
    public static final int KW_FIX=48;
    public static final int KW_REG=47;
    public static final int LINE_COMMENT=64;
    public static final int CONCAT=14;
    public static final int KW_ASSERT=54;
    public static final int STR_LIT=46;
    public static final int KW_QUERY=58;
    public static final int RANGE=20;
    public static final int INT=33;
    public static final int CHAR_LIT=42;
    public static final int RSQUARE=44;
    public static final int MINUS=43;
    public static final int REG=17;
    public static final int ASSERT=13;
    public static final int SEMI=29;
    public static final int CFGCHARSEQRANGE=26;
    public static final int CFGPLUS=9;
    public static final int COLON=32;
    public static final int WS=62;
    public static final int NEWLINE=61;
    public static final int KW_CONCAT=52;
    public static final int QUESTION=38;
    public static final int KW_OR=51;
    public static final int KW_CONTAINS=56;
    public static final int CHARSEQRANGE=21;
    public static final int OR=22;
    public static final int ASSIGN=5;
    public static final int PROGRAM=6;
    public static final int KW_STAR=50;
    public static final int EscapeSequence=60;
    public static final int BAR=35;
    public static final int KW_NOT=57;
    public static final int KW_CFG=34;
    public static final int NOTIN=23;

    // delegates
    // delegators


        public HampiParser(TokenStream input) {
            this(input, new RecognizerSharedState());
        }
        public HampiParser(TokenStream input, RecognizerSharedState state) {
            super(input, state);
        }
        
    protected TreeAdaptor adaptor = new CommonTreeAdaptor();

    public void setTreeAdaptor(TreeAdaptor adaptor) {
        this.adaptor = adaptor;
    }
    public TreeAdaptor getTreeAdaptor() {
        return adaptor;
    }

    @Override
    public String[] getTokenNames() { return HampiParser.tokenNames; }
    @Override
    public String getGrammarFileName() { return "src/hampi/parser/Hampi.g"; }


    public static class program_return extends ParserRuleReturnScope {
        Object tree;
        @Override
        public Object getTree() { return tree; }
    };

    // $ANTLR start program
    // src/hampi/parser/Hampi.g:47:2: program : ( statement SEMI )+ -> ^( PROGRAM ( statement )+ ) ;
    public final HampiParser.program_return program() throws RecognitionException {
        HampiParser.program_return retval = new HampiParser.program_return();
        retval.start = input.LT(1);

        Object root_0 = null;

        Token SEMI2=null;
        HampiParser.statement_return statement1 = null;


        Object SEMI2_tree=null;
        RewriteRuleTokenStream stream_SEMI=new RewriteRuleTokenStream(adaptor,"token SEMI");
        RewriteRuleSubtreeStream stream_statement=new RewriteRuleSubtreeStream(adaptor,"rule statement");
        try {
            // src/hampi/parser/Hampi.g:47:10: ( ( statement SEMI )+ -> ^( PROGRAM ( statement )+ ) )
            // src/hampi/parser/Hampi.g:47:12: ( statement SEMI )+
            {
            // src/hampi/parser/Hampi.g:47:12: ( statement SEMI )+
            int cnt1=0;
            loop1:
            do {
                int alt1=2;
                int LA1_0 = input.LA(1);

                if ( (LA1_0==KW_VAR||LA1_0==KW_CFG||LA1_0==KW_REG||(LA1_0>=KW_VAL && LA1_0<=KW_ASSERT)) ) {
                    alt1=1;
                }


                switch (alt1) {
            	case 1 :
            	    // src/hampi/parser/Hampi.g:47:13: statement SEMI
            	    {
            	    pushFollow(FOLLOW_statement_in_program276);
            	    statement1=statement();

            	    state._fsp--;
            	    if (state.failed) return retval;
            	    if ( state.backtracking==0 ){
                    stream_statement.add(statement1.getTree());
                  }
            	    SEMI2=(Token)match(input,SEMI,FOLLOW_SEMI_in_program278); if (state.failed) return retval; 
            	    if ( state.backtracking==0 ){
                    stream_SEMI.add(SEMI2);
                  }


            	    }
            	    break;

            	default :
            	    if ( cnt1 >= 1 ){
                    break loop1;
                  }
            	    if (state.backtracking>0) {state.failed=true; return retval;}
                        EarlyExitException eee =
                            new EarlyExitException(1, input);
                        throw eee;
                }
                cnt1++;
            } while (true);



            // AST REWRITE
            // elements: statement
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( state.backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = adaptor.nil();
            // 47:30: -> ^( PROGRAM ( statement )+ )
            {
                // src/hampi/parser/Hampi.g:47:33: ^( PROGRAM ( statement )+ )
                {
                Object root_1 = adaptor.nil();
                root_1 = adaptor.becomeRoot(adaptor.create(PROGRAM, "PROGRAM"), root_1);

                if ( !(stream_statement.hasNext()) )
                  throw new RewriteEarlyExitException();
                while ( stream_statement.hasNext() ) {
                    adaptor.addChild(root_1, stream_statement.nextTree());

                }
                stream_statement.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            retval.tree = root_0;retval.tree = root_0;}
            }

            retval.stop = input.LT(-1);

            if ( state.backtracking==0 ) {

            retval.tree = adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }
        finally {
        }
        return retval;
    }
    // $ANTLR end program

    public static class statement_return extends ParserRuleReturnScope {
        Object tree;
        @Override
        public Object getTree() { return tree; }
    };

    // $ANTLR start statement
    // src/hampi/parser/Hampi.g:49:2: statement : ( vardeclStmt | cfgStmt | regStmt | valDeclStmt | assertStmt );
    public final HampiParser.statement_return statement() throws RecognitionException {
        HampiParser.statement_return retval = new HampiParser.statement_return();
        retval.start = input.LT(1);

        Object root_0 = null;

        HampiParser.vardeclStmt_return vardeclStmt3 = null;

        HampiParser.cfgStmt_return cfgStmt4 = null;

        HampiParser.regStmt_return regStmt5 = null;

        HampiParser.valDeclStmt_return valDeclStmt6 = null;

        HampiParser.assertStmt_return assertStmt7 = null;



        try {
            // src/hampi/parser/Hampi.g:49:12: ( vardeclStmt | cfgStmt | regStmt | valDeclStmt | assertStmt )
            int alt2=5;
            switch ( input.LA(1) ) {
            case KW_VAR:
                {
                alt2=1;
                }
                break;
            case KW_CFG:
                {
                alt2=2;
                }
                break;
            case KW_REG:
                {
                alt2=3;
                }
                break;
            case KW_VAL:
                {
                alt2=4;
                }
                break;
            case KW_ASSERT:
                {
                alt2=5;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 2, 0, input);

                throw nvae;
            }

            switch (alt2) {
                case 1 :
                    // src/hampi/parser/Hampi.g:49:14: vardeclStmt
                    {
                    root_0 = adaptor.nil();

                    pushFollow(FOLLOW_vardeclStmt_in_statement299);
                    vardeclStmt3=vardeclStmt();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ){
                      adaptor.addChild(root_0, vardeclStmt3.getTree());
                    }

                    }
                    break;
                case 2 :
                    // src/hampi/parser/Hampi.g:50:14: cfgStmt
                    {
                    root_0 = adaptor.nil();

                    pushFollow(FOLLOW_cfgStmt_in_statement315);
                    cfgStmt4=cfgStmt();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ){
                      adaptor.addChild(root_0, cfgStmt4.getTree());
                    }

                    }
                    break;
                case 3 :
                    // src/hampi/parser/Hampi.g:51:14: regStmt
                    {
                    root_0 = adaptor.nil();

                    pushFollow(FOLLOW_regStmt_in_statement330);
                    regStmt5=regStmt();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ){
                      adaptor.addChild(root_0, regStmt5.getTree());
                    }

                    }
                    break;
                case 4 :
                    // src/hampi/parser/Hampi.g:52:14: valDeclStmt
                    {
                    root_0 = adaptor.nil();

                    pushFollow(FOLLOW_valDeclStmt_in_statement345);
                    valDeclStmt6=valDeclStmt();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ){
                      adaptor.addChild(root_0, valDeclStmt6.getTree());
                    }

                    }
                    break;
                case 5 :
                    // src/hampi/parser/Hampi.g:53:14: assertStmt
                    {
                    root_0 = adaptor.nil();

                    pushFollow(FOLLOW_assertStmt_in_statement360);
                    assertStmt7=assertStmt();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ){
                      adaptor.addChild(root_0, assertStmt7.getTree());
                    }

                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( state.backtracking==0 ) {

            retval.tree = adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }
        finally {
        }
        return retval;
    }
    // $ANTLR end statement

    public static class vardeclStmt_return extends ParserRuleReturnScope {
        Object tree;
        @Override
        public Object getTree() { return tree; }
    };

    // $ANTLR start vardeclStmt
    // src/hampi/parser/Hampi.g:56:2: vardeclStmt : ( KW_VAR ID COLON INT ) -> ^( VAR ID INT ) ;
    public final HampiParser.vardeclStmt_return vardeclStmt() throws RecognitionException {
        HampiParser.vardeclStmt_return retval = new HampiParser.vardeclStmt_return();
        retval.start = input.LT(1);

        Object root_0 = null;

        Token KW_VAR8=null;
        Token ID9=null;
        Token COLON10=null;
        Token INT11=null;

        Object KW_VAR8_tree=null;
        Object ID9_tree=null;
        Object COLON10_tree=null;
        Object INT11_tree=null;
        RewriteRuleTokenStream stream_COLON=new RewriteRuleTokenStream(adaptor,"token COLON");
        RewriteRuleTokenStream stream_INT=new RewriteRuleTokenStream(adaptor,"token INT");
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_KW_VAR=new RewriteRuleTokenStream(adaptor,"token KW_VAR");

        try {
            // src/hampi/parser/Hampi.g:56:14: ( ( KW_VAR ID COLON INT ) -> ^( VAR ID INT ) )
            // src/hampi/parser/Hampi.g:56:16: ( KW_VAR ID COLON INT )
            {
            // src/hampi/parser/Hampi.g:56:16: ( KW_VAR ID COLON INT )
            // src/hampi/parser/Hampi.g:56:17: KW_VAR ID COLON INT
            {
            KW_VAR8=(Token)match(input,KW_VAR,FOLLOW_KW_VAR_in_vardeclStmt393); if (state.failed) return retval; 
            if ( state.backtracking==0 ){
              stream_KW_VAR.add(KW_VAR8);
            }

            ID9=(Token)match(input,ID,FOLLOW_ID_in_vardeclStmt395); if (state.failed) return retval; 
            if ( state.backtracking==0 ){
              stream_ID.add(ID9);
            }

            COLON10=(Token)match(input,COLON,FOLLOW_COLON_in_vardeclStmt397); if (state.failed) return retval; 
            if ( state.backtracking==0 ){
              stream_COLON.add(COLON10);
            }

            INT11=(Token)match(input,INT,FOLLOW_INT_in_vardeclStmt399); if (state.failed) return retval; 
            if ( state.backtracking==0 ){
              stream_INT.add(INT11);
            }


            }



            // AST REWRITE
            // elements: ID, INT
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( state.backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = adaptor.nil();
            // 56:38: -> ^( VAR ID INT )
            {
                // src/hampi/parser/Hampi.g:56:41: ^( VAR ID INT )
                {
                Object root_1 = adaptor.nil();
                root_1 = adaptor.becomeRoot(adaptor.create(VAR, "VAR"), root_1);

                adaptor.addChild(root_1, stream_ID.nextNode());
                adaptor.addChild(root_1, stream_INT.nextNode());

                adaptor.addChild(root_0, root_1);
                }

            }

            retval.tree = root_0;retval.tree = root_0;}
            }

            retval.stop = input.LT(-1);

            if ( state.backtracking==0 ) {

            retval.tree = adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }
        finally {
        }
        return retval;
    }
    // $ANTLR end vardeclStmt

    public static class cfgStmt_return extends ParserRuleReturnScope {
        Object tree;
        @Override
        public Object getTree() { return tree; }
    };

    // $ANTLR start cfgStmt
    // src/hampi/parser/Hampi.g:58:2: cfgStmt : ( KW_CFG cfgProduction ) -> ^( CFG cfgProduction ) ;
    public final HampiParser.cfgStmt_return cfgStmt() throws RecognitionException {
        HampiParser.cfgStmt_return retval = new HampiParser.cfgStmt_return();
        retval.start = input.LT(1);

        Object root_0 = null;

        Token KW_CFG12=null;
        HampiParser.cfgProduction_return cfgProduction13 = null;


        Object KW_CFG12_tree=null;
        RewriteRuleTokenStream stream_KW_CFG=new RewriteRuleTokenStream(adaptor,"token KW_CFG");
        RewriteRuleSubtreeStream stream_cfgProduction=new RewriteRuleSubtreeStream(adaptor,"rule cfgProduction");
        try {
            // src/hampi/parser/Hampi.g:58:10: ( ( KW_CFG cfgProduction ) -> ^( CFG cfgProduction ) )
            // src/hampi/parser/Hampi.g:58:12: ( KW_CFG cfgProduction )
            {
            // src/hampi/parser/Hampi.g:58:12: ( KW_CFG cfgProduction )
            // src/hampi/parser/Hampi.g:58:13: KW_CFG cfgProduction
            {
            KW_CFG12=(Token)match(input,KW_CFG,FOLLOW_KW_CFG_in_cfgStmt421); if (state.failed) return retval; 
            if ( state.backtracking==0 ){
              stream_KW_CFG.add(KW_CFG12);
            }

            pushFollow(FOLLOW_cfgProduction_in_cfgStmt423);
            cfgProduction13=cfgProduction();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ){
              stream_cfgProduction.add(cfgProduction13.getTree());
            }

            }



            // AST REWRITE
            // elements: cfgProduction
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( state.backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = adaptor.nil();
            // 58:35: -> ^( CFG cfgProduction )
            {
                // src/hampi/parser/Hampi.g:58:38: ^( CFG cfgProduction )
                {
                Object root_1 = adaptor.nil();
                root_1 = adaptor.becomeRoot(adaptor.create(CFG, "CFG"), root_1);

                adaptor.addChild(root_1, stream_cfgProduction.nextTree());

                adaptor.addChild(root_0, root_1);
                }

            }

            retval.tree = root_0;retval.tree = root_0;}
            }

            retval.stop = input.LT(-1);

            if ( state.backtracking==0 ) {

            retval.tree = adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }
        finally {
        }
        return retval;
    }
    // $ANTLR end cfgStmt

    public static class cfgProduction_return extends ParserRuleReturnScope {
        Object tree;
        @Override
        public Object getTree() { return tree; }
    };

    // $ANTLR start cfgProduction
    // src/hampi/parser/Hampi.g:60:2: cfgProduction : ( ID ASSIGN cfgProductionSet ) -> ^( CFGPROD ID cfgProductionSet ) ;
    public final HampiParser.cfgProduction_return cfgProduction() throws RecognitionException {
        HampiParser.cfgProduction_return retval = new HampiParser.cfgProduction_return();
        retval.start = input.LT(1);

        Object root_0 = null;

        Token ID14=null;
        Token ASSIGN15=null;
        HampiParser.cfgProductionSet_return cfgProductionSet16 = null;


        Object ID14_tree=null;
        Object ASSIGN15_tree=null;
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_ASSIGN=new RewriteRuleTokenStream(adaptor,"token ASSIGN");
        RewriteRuleSubtreeStream stream_cfgProductionSet=new RewriteRuleSubtreeStream(adaptor,"rule cfgProductionSet");
        try {
            // src/hampi/parser/Hampi.g:60:16: ( ( ID ASSIGN cfgProductionSet ) -> ^( CFGPROD ID cfgProductionSet ) )
            // src/hampi/parser/Hampi.g:60:18: ( ID ASSIGN cfgProductionSet )
            {
            // src/hampi/parser/Hampi.g:60:18: ( ID ASSIGN cfgProductionSet )
            // src/hampi/parser/Hampi.g:60:19: ID ASSIGN cfgProductionSet
            {
            ID14=(Token)match(input,ID,FOLLOW_ID_in_cfgProduction443); if (state.failed) return retval; 
            if ( state.backtracking==0 ){
              stream_ID.add(ID14);
            }

            ASSIGN15=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_cfgProduction445); if (state.failed) return retval; 
            if ( state.backtracking==0 ){
              stream_ASSIGN.add(ASSIGN15);
            }

            pushFollow(FOLLOW_cfgProductionSet_in_cfgProduction448);
            cfgProductionSet16=cfgProductionSet();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ){
              stream_cfgProductionSet.add(cfgProductionSet16.getTree());
            }

            }



            // AST REWRITE
            // elements: cfgProductionSet, ID
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( state.backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = adaptor.nil();
            // 60:49: -> ^( CFGPROD ID cfgProductionSet )
            {
                // src/hampi/parser/Hampi.g:60:52: ^( CFGPROD ID cfgProductionSet )
                {
                Object root_1 = adaptor.nil();
                root_1 = adaptor.becomeRoot(adaptor.create(CFGPROD, "CFGPROD"), root_1);

                adaptor.addChild(root_1, stream_ID.nextNode());
                adaptor.addChild(root_1, stream_cfgProductionSet.nextTree());

                adaptor.addChild(root_0, root_1);
                }

            }

            retval.tree = root_0;retval.tree = root_0;}
            }

            retval.stop = input.LT(-1);

            if ( state.backtracking==0 ) {

            retval.tree = adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }
        finally {
        }
        return retval;
    }
    // $ANTLR end cfgProduction

    public static class cfgProductionSet_return extends ParserRuleReturnScope {
        Object tree;
        @Override
        public Object getTree() { return tree; }
    };

    // $ANTLR start cfgProductionSet
    // src/hampi/parser/Hampi.g:62:2: cfgProductionSet : ( cfgProductionElementSet ( BAR cfgProductionElementSet )* ) -> ( cfgProductionElementSet )+ ;
    public final HampiParser.cfgProductionSet_return cfgProductionSet() throws RecognitionException {
        HampiParser.cfgProductionSet_return retval = new HampiParser.cfgProductionSet_return();
        retval.start = input.LT(1);

        Object root_0 = null;

        Token BAR18=null;
        HampiParser.cfgProductionElementSet_return cfgProductionElementSet17 = null;

        HampiParser.cfgProductionElementSet_return cfgProductionElementSet19 = null;


        Object BAR18_tree=null;
        RewriteRuleTokenStream stream_BAR=new RewriteRuleTokenStream(adaptor,"token BAR");
        RewriteRuleSubtreeStream stream_cfgProductionElementSet=new RewriteRuleSubtreeStream(adaptor,"rule cfgProductionElementSet");
        try {
            // src/hampi/parser/Hampi.g:62:19: ( ( cfgProductionElementSet ( BAR cfgProductionElementSet )* ) -> ( cfgProductionElementSet )+ )
            // src/hampi/parser/Hampi.g:62:21: ( cfgProductionElementSet ( BAR cfgProductionElementSet )* )
            {
            // src/hampi/parser/Hampi.g:62:21: ( cfgProductionElementSet ( BAR cfgProductionElementSet )* )
            // src/hampi/parser/Hampi.g:62:22: cfgProductionElementSet ( BAR cfgProductionElementSet )*
            {
            pushFollow(FOLLOW_cfgProductionElementSet_in_cfgProductionSet472);
            cfgProductionElementSet17=cfgProductionElementSet();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ){
              stream_cfgProductionElementSet.add(cfgProductionElementSet17.getTree());
            }
            // src/hampi/parser/Hampi.g:62:46: ( BAR cfgProductionElementSet )*
            loop3:
            do {
                int alt3=2;
                int LA3_0 = input.LA(1);

                if ( (LA3_0==BAR) ) {
                    alt3=1;
                }


                switch (alt3) {
            	case 1 :
            	    // src/hampi/parser/Hampi.g:62:47: BAR cfgProductionElementSet
            	    {
            	    BAR18=(Token)match(input,BAR,FOLLOW_BAR_in_cfgProductionSet475); if (state.failed) return retval; 
            	    if ( state.backtracking==0 ){
                    stream_BAR.add(BAR18);
                  }

            	    pushFollow(FOLLOW_cfgProductionElementSet_in_cfgProductionSet477);
            	    cfgProductionElementSet19=cfgProductionElementSet();

            	    state._fsp--;
            	    if (state.failed) return retval;
            	    if ( state.backtracking==0 ){
                    stream_cfgProductionElementSet.add(cfgProductionElementSet19.getTree());
                  }

            	    }
            	    break;

            	default :
            	    break loop3;
                }
            } while (true);


            }



            // AST REWRITE
            // elements: cfgProductionElementSet
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( state.backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = adaptor.nil();
            // 62:78: -> ( cfgProductionElementSet )+
            {
                if ( !(stream_cfgProductionElementSet.hasNext()) )
                  throw new RewriteEarlyExitException();
                while ( stream_cfgProductionElementSet.hasNext() ) {
                    adaptor.addChild(root_0, stream_cfgProductionElementSet.nextTree());

                }
                stream_cfgProductionElementSet.reset();

            }

            retval.tree = root_0;retval.tree = root_0;}
            }

            retval.stop = input.LT(-1);

            if ( state.backtracking==0 ) {

            retval.tree = adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }
        finally {
        }
        return retval;
    }
    // $ANTLR end cfgProductionSet

    public static class cfgProductionElementSet_return extends ParserRuleReturnScope {
        Object tree;
        @Override
        public Object getTree() { return tree; }
    };

    // $ANTLR start cfgProductionElementSet
    // src/hampi/parser/Hampi.g:64:2: cfgProductionElementSet : ( ( cfgProductionElement )* ) -> ^( CFGPRODELEMSET ( cfgProductionElement )* ) ;
    public final HampiParser.cfgProductionElementSet_return cfgProductionElementSet() throws RecognitionException {
        HampiParser.cfgProductionElementSet_return retval = new HampiParser.cfgProductionElementSet_return();
        retval.start = input.LT(1);

        Object root_0 = null;

        HampiParser.cfgProductionElement_return cfgProductionElement20 = null;


        RewriteRuleSubtreeStream stream_cfgProductionElement=new RewriteRuleSubtreeStream(adaptor,"rule cfgProductionElement");
        try {
            // src/hampi/parser/Hampi.g:64:26: ( ( ( cfgProductionElement )* ) -> ^( CFGPRODELEMSET ( cfgProductionElement )* ) )
            // src/hampi/parser/Hampi.g:64:28: ( ( cfgProductionElement )* )
            {
            // src/hampi/parser/Hampi.g:64:28: ( ( cfgProductionElement )* )
            // src/hampi/parser/Hampi.g:64:29: ( cfgProductionElement )*
            {
            // src/hampi/parser/Hampi.g:64:29: ( cfgProductionElement )*
            loop4:
            do {
                int alt4=2;
                int LA4_0 = input.LA(1);

                if ( (LA4_0==ID||LA4_0==LPAREN||LA4_0==LSQUARE||(LA4_0>=CHAR_SEQ && LA4_0<=STR_LIT)) ) {
                    alt4=1;
                }


                switch (alt4) {
            	case 1 :
            	    // src/hampi/parser/Hampi.g:0:0: cfgProductionElement
            	    {
            	    pushFollow(FOLLOW_cfgProductionElement_in_cfgProductionElementSet496);
            	    cfgProductionElement20=cfgProductionElement();

            	    state._fsp--;
            	    if (state.failed) return retval;
            	    if ( state.backtracking==0 ){
                    stream_cfgProductionElement.add(cfgProductionElement20.getTree());
                  }

            	    }
            	    break;

            	default :
            	    break loop4;
                }
            } while (true);


            }



            // AST REWRITE
            // elements: cfgProductionElement
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( state.backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = adaptor.nil();
            // 64:53: -> ^( CFGPRODELEMSET ( cfgProductionElement )* )
            {
                // src/hampi/parser/Hampi.g:64:56: ^( CFGPRODELEMSET ( cfgProductionElement )* )
                {
                Object root_1 = adaptor.nil();
                root_1 = adaptor.becomeRoot(adaptor.create(CFGPRODELEMSET, "CFGPRODELEMSET"), root_1);

                // src/hampi/parser/Hampi.g:64:73: ( cfgProductionElement )*
                while ( stream_cfgProductionElement.hasNext() ) {
                    adaptor.addChild(root_1, stream_cfgProductionElement.nextTree());

                }
                stream_cfgProductionElement.reset();

                adaptor.addChild(root_0, root_1);
                }

            }

            retval.tree = root_0;retval.tree = root_0;}
            }

            retval.stop = input.LT(-1);

            if ( state.backtracking==0 ) {

            retval.tree = adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }
        finally {
        }
        return retval;
    }
    // $ANTLR end cfgProductionElementSet

    public static class cfgProductionElement_return extends ParserRuleReturnScope {
        Object tree;
        @Override
        public Object getTree() { return tree; }
    };

    // $ANTLR start cfgProductionElement
    // src/hampi/parser/Hampi.g:66:2: cfgProductionElement : ( cfgTerminal -> cfgTerminal | cfgNonterminal -> cfgNonterminal | LPAREN cfgNonterminal RPAREN QUESTION -> ^( CFGOPTION cfgNonterminal ) | LPAREN cfgNonterminal RPAREN STAR -> ^( CFGSTAR cfgNonterminal ) | LPAREN cfgNonterminal RPAREN PLUS -> ^( CFGPLUS cfgNonterminal ) | LSQUARE CHAR_LIT MINUS CHAR_LIT RSQUARE -> ^( CFGCHARRANGE CHAR_LIT CHAR_LIT ) | LSQUARE CHAR_SEQ MINUS CHAR_SEQ RSQUARE -> ^( CFGCHARSEQRANGE CHAR_SEQ CHAR_SEQ ) );
    public final HampiParser.cfgProductionElement_return cfgProductionElement() throws RecognitionException {
        HampiParser.cfgProductionElement_return retval = new HampiParser.cfgProductionElement_return();
        retval.start = input.LT(1);

        Object root_0 = null;

        Token LPAREN23=null;
        Token RPAREN25=null;
        Token QUESTION26=null;
        Token LPAREN27=null;
        Token RPAREN29=null;
        Token STAR30=null;
        Token LPAREN31=null;
        Token RPAREN33=null;
        Token PLUS34=null;
        Token LSQUARE35=null;
        Token CHAR_LIT36=null;
        Token MINUS37=null;
        Token CHAR_LIT38=null;
        Token RSQUARE39=null;
        Token LSQUARE40=null;
        Token CHAR_SEQ41=null;
        Token MINUS42=null;
        Token CHAR_SEQ43=null;
        Token RSQUARE44=null;
        HampiParser.cfgTerminal_return cfgTerminal21 = null;

        HampiParser.cfgNonterminal_return cfgNonterminal22 = null;

        HampiParser.cfgNonterminal_return cfgNonterminal24 = null;

        HampiParser.cfgNonterminal_return cfgNonterminal28 = null;

        HampiParser.cfgNonterminal_return cfgNonterminal32 = null;


        Object LPAREN23_tree=null;
        Object RPAREN25_tree=null;
        Object QUESTION26_tree=null;
        Object LPAREN27_tree=null;
        Object RPAREN29_tree=null;
        Object STAR30_tree=null;
        Object LPAREN31_tree=null;
        Object RPAREN33_tree=null;
        Object PLUS34_tree=null;
        Object LSQUARE35_tree=null;
        Object CHAR_LIT36_tree=null;
        Object MINUS37_tree=null;
        Object CHAR_LIT38_tree=null;
        Object RSQUARE39_tree=null;
        Object LSQUARE40_tree=null;
        Object CHAR_SEQ41_tree=null;
        Object MINUS42_tree=null;
        Object CHAR_SEQ43_tree=null;
        Object RSQUARE44_tree=null;
        RewriteRuleTokenStream stream_CHAR_SEQ=new RewriteRuleTokenStream(adaptor,"token CHAR_SEQ");
        RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
        RewriteRuleTokenStream stream_PLUS=new RewriteRuleTokenStream(adaptor,"token PLUS");
        RewriteRuleTokenStream stream_STAR=new RewriteRuleTokenStream(adaptor,"token STAR");
        RewriteRuleTokenStream stream_LSQUARE=new RewriteRuleTokenStream(adaptor,"token LSQUARE");
        RewriteRuleTokenStream stream_CHAR_LIT=new RewriteRuleTokenStream(adaptor,"token CHAR_LIT");
        RewriteRuleTokenStream stream_QUESTION=new RewriteRuleTokenStream(adaptor,"token QUESTION");
        RewriteRuleTokenStream stream_MINUS=new RewriteRuleTokenStream(adaptor,"token MINUS");
        RewriteRuleTokenStream stream_RSQUARE=new RewriteRuleTokenStream(adaptor,"token RSQUARE");
        RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
        RewriteRuleSubtreeStream stream_cfgNonterminal=new RewriteRuleSubtreeStream(adaptor,"rule cfgNonterminal");
        RewriteRuleSubtreeStream stream_cfgTerminal=new RewriteRuleSubtreeStream(adaptor,"rule cfgTerminal");
        try {
            // src/hampi/parser/Hampi.g:66:23: ( cfgTerminal -> cfgTerminal | cfgNonterminal -> cfgNonterminal | LPAREN cfgNonterminal RPAREN QUESTION -> ^( CFGOPTION cfgNonterminal ) | LPAREN cfgNonterminal RPAREN STAR -> ^( CFGSTAR cfgNonterminal ) | LPAREN cfgNonterminal RPAREN PLUS -> ^( CFGPLUS cfgNonterminal ) | LSQUARE CHAR_LIT MINUS CHAR_LIT RSQUARE -> ^( CFGCHARRANGE CHAR_LIT CHAR_LIT ) | LSQUARE CHAR_SEQ MINUS CHAR_SEQ RSQUARE -> ^( CFGCHARSEQRANGE CHAR_SEQ CHAR_SEQ ) )
            int alt5=7;
            alt5 = dfa5.predict(input);
            switch (alt5) {
                case 1 :
                    // src/hampi/parser/Hampi.g:66:25: cfgTerminal
                    {
                    pushFollow(FOLLOW_cfgTerminal_in_cfgProductionElement519);
                    cfgTerminal21=cfgTerminal();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ){
                      stream_cfgTerminal.add(cfgTerminal21.getTree());
                    }


                    // AST REWRITE
                    // elements: cfgTerminal
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = adaptor.nil();
                    // 66:37: -> cfgTerminal
                    {
                        adaptor.addChild(root_0, stream_cfgTerminal.nextTree());

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;
                case 2 :
                    // src/hampi/parser/Hampi.g:67:25: cfgNonterminal
                    {
                    pushFollow(FOLLOW_cfgNonterminal_in_cfgProductionElement549);
                    cfgNonterminal22=cfgNonterminal();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ){
                      stream_cfgNonterminal.add(cfgNonterminal22.getTree());
                    }


                    // AST REWRITE
                    // elements: cfgNonterminal
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = adaptor.nil();
                    // 67:40: -> cfgNonterminal
                    {
                        adaptor.addChild(root_0, stream_cfgNonterminal.nextTree());

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;
                case 3 :
                    // src/hampi/parser/Hampi.g:68:25: LPAREN cfgNonterminal RPAREN QUESTION
                    {
                    LPAREN23=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_cfgProductionElement579); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_LPAREN.add(LPAREN23);
                    }

                    pushFollow(FOLLOW_cfgNonterminal_in_cfgProductionElement581);
                    cfgNonterminal24=cfgNonterminal();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ){
                      stream_cfgNonterminal.add(cfgNonterminal24.getTree());
                    }
                    RPAREN25=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_cfgProductionElement583); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_RPAREN.add(RPAREN25);
                    }

                    QUESTION26=(Token)match(input,QUESTION,FOLLOW_QUESTION_in_cfgProductionElement585); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_QUESTION.add(QUESTION26);
                    }



                    // AST REWRITE
                    // elements: cfgNonterminal
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = adaptor.nil();
                    // 68:63: -> ^( CFGOPTION cfgNonterminal )
                    {
                        // src/hampi/parser/Hampi.g:68:66: ^( CFGOPTION cfgNonterminal )
                        {
                        Object root_1 = adaptor.nil();
                        root_1 = adaptor.becomeRoot(adaptor.create(CFGOPTION, "CFGOPTION"), root_1);

                        adaptor.addChild(root_1, stream_cfgNonterminal.nextTree());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;
                case 4 :
                    // src/hampi/parser/Hampi.g:69:25: LPAREN cfgNonterminal RPAREN STAR
                    {
                    LPAREN27=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_cfgProductionElement619); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_LPAREN.add(LPAREN27);
                    }

                    pushFollow(FOLLOW_cfgNonterminal_in_cfgProductionElement621);
                    cfgNonterminal28=cfgNonterminal();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ){
                      stream_cfgNonterminal.add(cfgNonterminal28.getTree());
                    }
                    RPAREN29=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_cfgProductionElement623); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_RPAREN.add(RPAREN29);
                    }

                    STAR30=(Token)match(input,STAR,FOLLOW_STAR_in_cfgProductionElement625); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_STAR.add(STAR30);
                    }



                    // AST REWRITE
                    // elements: cfgNonterminal
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = adaptor.nil();
                    // 69:63: -> ^( CFGSTAR cfgNonterminal )
                    {
                        // src/hampi/parser/Hampi.g:69:66: ^( CFGSTAR cfgNonterminal )
                        {
                        Object root_1 = adaptor.nil();
                        root_1 = adaptor.becomeRoot(adaptor.create(CFGSTAR, "CFGSTAR"), root_1);

                        adaptor.addChild(root_1, stream_cfgNonterminal.nextTree());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;
                case 5 :
                    // src/hampi/parser/Hampi.g:70:25: LPAREN cfgNonterminal RPAREN PLUS
                    {
                    LPAREN31=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_cfgProductionElement667); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_LPAREN.add(LPAREN31);
                    }

                    pushFollow(FOLLOW_cfgNonterminal_in_cfgProductionElement669);
                    cfgNonterminal32=cfgNonterminal();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ){
                      stream_cfgNonterminal.add(cfgNonterminal32.getTree());
                    }
                    RPAREN33=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_cfgProductionElement671); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_RPAREN.add(RPAREN33);
                    }

                    PLUS34=(Token)match(input,PLUS,FOLLOW_PLUS_in_cfgProductionElement673); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_PLUS.add(PLUS34);
                    }



                    // AST REWRITE
                    // elements: cfgNonterminal
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = adaptor.nil();
                    // 70:60: -> ^( CFGPLUS cfgNonterminal )
                    {
                        // src/hampi/parser/Hampi.g:70:63: ^( CFGPLUS cfgNonterminal )
                        {
                        Object root_1 = adaptor.nil();
                        root_1 = adaptor.becomeRoot(adaptor.create(CFGPLUS, "CFGPLUS"), root_1);

                        adaptor.addChild(root_1, stream_cfgNonterminal.nextTree());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;
                case 6 :
                    // src/hampi/parser/Hampi.g:71:25: LSQUARE CHAR_LIT MINUS CHAR_LIT RSQUARE
                    {
                    LSQUARE35=(Token)match(input,LSQUARE,FOLLOW_LSQUARE_in_cfgProductionElement712); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_LSQUARE.add(LSQUARE35);
                    }

                    CHAR_LIT36=(Token)match(input,CHAR_LIT,FOLLOW_CHAR_LIT_in_cfgProductionElement714); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_CHAR_LIT.add(CHAR_LIT36);
                    }

                    MINUS37=(Token)match(input,MINUS,FOLLOW_MINUS_in_cfgProductionElement716); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_MINUS.add(MINUS37);
                    }

                    CHAR_LIT38=(Token)match(input,CHAR_LIT,FOLLOW_CHAR_LIT_in_cfgProductionElement718); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_CHAR_LIT.add(CHAR_LIT38);
                    }

                    RSQUARE39=(Token)match(input,RSQUARE,FOLLOW_RSQUARE_in_cfgProductionElement720); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_RSQUARE.add(RSQUARE39);
                    }



                    // AST REWRITE
                    // elements: CHAR_LIT, CHAR_LIT
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = adaptor.nil();
                    // 71:65: -> ^( CFGCHARRANGE CHAR_LIT CHAR_LIT )
                    {
                        // src/hampi/parser/Hampi.g:71:68: ^( CFGCHARRANGE CHAR_LIT CHAR_LIT )
                        {
                        Object root_1 = adaptor.nil();
                        root_1 = adaptor.becomeRoot(adaptor.create(CFGCHARRANGE, "CFGCHARRANGE"), root_1);

                        adaptor.addChild(root_1, stream_CHAR_LIT.nextNode());
                        adaptor.addChild(root_1, stream_CHAR_LIT.nextNode());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;
                case 7 :
                    // src/hampi/parser/Hampi.g:72:28: LSQUARE CHAR_SEQ MINUS CHAR_SEQ RSQUARE
                    {
                    LSQUARE40=(Token)match(input,LSQUARE,FOLLOW_LSQUARE_in_cfgProductionElement759); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_LSQUARE.add(LSQUARE40);
                    }

                    CHAR_SEQ41=(Token)match(input,CHAR_SEQ,FOLLOW_CHAR_SEQ_in_cfgProductionElement761); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_CHAR_SEQ.add(CHAR_SEQ41);
                    }

                    MINUS42=(Token)match(input,MINUS,FOLLOW_MINUS_in_cfgProductionElement763); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_MINUS.add(MINUS42);
                    }

                    CHAR_SEQ43=(Token)match(input,CHAR_SEQ,FOLLOW_CHAR_SEQ_in_cfgProductionElement765); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_CHAR_SEQ.add(CHAR_SEQ43);
                    }

                    RSQUARE44=(Token)match(input,RSQUARE,FOLLOW_RSQUARE_in_cfgProductionElement767); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_RSQUARE.add(RSQUARE44);
                    }



                    // AST REWRITE
                    // elements: CHAR_SEQ, CHAR_SEQ
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = adaptor.nil();
                    // 72:68: -> ^( CFGCHARSEQRANGE CHAR_SEQ CHAR_SEQ )
                    {
                        // src/hampi/parser/Hampi.g:72:71: ^( CFGCHARSEQRANGE CHAR_SEQ CHAR_SEQ )
                        {
                        Object root_1 = adaptor.nil();
                        root_1 = adaptor.becomeRoot(adaptor.create(CFGCHARSEQRANGE, "CFGCHARSEQRANGE"), root_1);

                        adaptor.addChild(root_1, stream_CHAR_SEQ.nextNode());
                        adaptor.addChild(root_1, stream_CHAR_SEQ.nextNode());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( state.backtracking==0 ) {

            retval.tree = adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }
        finally {
        }
        return retval;
    }
    // $ANTLR end cfgProductionElement

    public static class cfgTerminal_return extends ParserRuleReturnScope {
        Object tree;
        @Override
        public Object getTree() { return tree; }
    };

    // $ANTLR start cfgTerminal
    // src/hampi/parser/Hampi.g:75:5: cfgTerminal : ( STR_LIT | CHAR_SEQ );
    public final HampiParser.cfgTerminal_return cfgTerminal() throws RecognitionException {
        HampiParser.cfgTerminal_return retval = new HampiParser.cfgTerminal_return();
        retval.start = input.LT(1);

        Object root_0 = null;

        Token set45=null;

        Object set45_tree=null;

        try {
            // src/hampi/parser/Hampi.g:75:17: ( STR_LIT | CHAR_SEQ )
            // src/hampi/parser/Hampi.g:
            {
            root_0 = adaptor.nil();

            set45=input.LT(1);
            if ( (input.LA(1)>=CHAR_SEQ && input.LA(1)<=STR_LIT) ) {
                input.consume();
                if ( state.backtracking==0 ){
                  adaptor.addChild(root_0, adaptor.create(set45));
                }
                state.errorRecovery=false;state.failed=false;
            }
            else {
                if (state.backtracking>0) {state.failed=true; return retval;}
                MismatchedSetException mse = new MismatchedSetException(null,input);
                throw mse;
            }


            }

            retval.stop = input.LT(-1);

            if ( state.backtracking==0 ) {

            retval.tree = adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }
        finally {
        }
        return retval;
    }
    // $ANTLR end cfgTerminal

    public static class cfgNonterminal_return extends ParserRuleReturnScope {
        Object tree;
        @Override
        public Object getTree() { return tree; }
    };

    // $ANTLR start cfgNonterminal
    // src/hampi/parser/Hampi.g:78:5: cfgNonterminal : ID ;
    public final HampiParser.cfgNonterminal_return cfgNonterminal() throws RecognitionException {
        HampiParser.cfgNonterminal_return retval = new HampiParser.cfgNonterminal_return();
        retval.start = input.LT(1);

        Object root_0 = null;

        Token ID46=null;

        Object ID46_tree=null;

        try {
            // src/hampi/parser/Hampi.g:78:20: ( ID )
            // src/hampi/parser/Hampi.g:78:22: ID
            {
            root_0 = adaptor.nil();

            ID46=(Token)match(input,ID,FOLLOW_ID_in_cfgNonterminal868); if (state.failed) return retval;
            if ( state.backtracking==0 ) {
            ID46_tree = adaptor.create(ID46);
            adaptor.addChild(root_0, ID46_tree);
            }

            }

            retval.stop = input.LT(-1);

            if ( state.backtracking==0 ) {

            retval.tree = adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }
        finally {
        }
        return retval;
    }
    // $ANTLR end cfgNonterminal

    public static class regStmt_return extends ParserRuleReturnScope {
        Object tree;
        @Override
        public Object getTree() { return tree; }
    };

    // $ANTLR start regStmt
    // src/hampi/parser/Hampi.g:80:5: regStmt : ( KW_REG ID ASSIGN regDefinition ) -> ^( REG ID regDefinition ) ;
    public final HampiParser.regStmt_return regStmt() throws RecognitionException {
        HampiParser.regStmt_return retval = new HampiParser.regStmt_return();
        retval.start = input.LT(1);

        Object root_0 = null;

        Token KW_REG47=null;
        Token ID48=null;
        Token ASSIGN49=null;
        HampiParser.regDefinition_return regDefinition50 = null;


        Object KW_REG47_tree=null;
        Object ID48_tree=null;
        Object ASSIGN49_tree=null;
        RewriteRuleTokenStream stream_KW_REG=new RewriteRuleTokenStream(adaptor,"token KW_REG");
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_ASSIGN=new RewriteRuleTokenStream(adaptor,"token ASSIGN");
        RewriteRuleSubtreeStream stream_regDefinition=new RewriteRuleSubtreeStream(adaptor,"rule regDefinition");
        try {
            // src/hampi/parser/Hampi.g:80:13: ( ( KW_REG ID ASSIGN regDefinition ) -> ^( REG ID regDefinition ) )
            // src/hampi/parser/Hampi.g:80:15: ( KW_REG ID ASSIGN regDefinition )
            {
            // src/hampi/parser/Hampi.g:80:15: ( KW_REG ID ASSIGN regDefinition )
            // src/hampi/parser/Hampi.g:80:16: KW_REG ID ASSIGN regDefinition
            {
            KW_REG47=(Token)match(input,KW_REG,FOLLOW_KW_REG_in_regStmt885); if (state.failed) return retval; 
            if ( state.backtracking==0 ){
              stream_KW_REG.add(KW_REG47);
            }

            ID48=(Token)match(input,ID,FOLLOW_ID_in_regStmt887); if (state.failed) return retval; 
            if ( state.backtracking==0 ){
              stream_ID.add(ID48);
            }

            ASSIGN49=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_regStmt889); if (state.failed) return retval; 
            if ( state.backtracking==0 ){
              stream_ASSIGN.add(ASSIGN49);
            }

            pushFollow(FOLLOW_regDefinition_in_regStmt891);
            regDefinition50=regDefinition();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ){
              stream_regDefinition.add(regDefinition50.getTree());
            }

            }



            // AST REWRITE
            // elements: regDefinition, ID
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( state.backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = adaptor.nil();
            // 80:48: -> ^( REG ID regDefinition )
            {
                // src/hampi/parser/Hampi.g:80:51: ^( REG ID regDefinition )
                {
                Object root_1 = adaptor.nil();
                root_1 = adaptor.becomeRoot(adaptor.create(REG, "REG"), root_1);

                adaptor.addChild(root_1, stream_ID.nextNode());
                adaptor.addChild(root_1, stream_regDefinition.nextTree());

                adaptor.addChild(root_0, root_1);
                }

            }

            retval.tree = root_0;retval.tree = root_0;}
            }

            retval.stop = input.LT(-1);

            if ( state.backtracking==0 ) {

            retval.tree = adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }
        finally {
        }
        return retval;
    }
    // $ANTLR end regStmt

    public static class regDefinition_return extends ParserRuleReturnScope {
        Object tree;
        @Override
        public Object getTree() { return tree; }
    };

    // $ANTLR start regDefinition
    // src/hampi/parser/Hampi.g:82:5: regDefinition : ( ID -> ID | STR_LIT -> STR_LIT | CHAR_SEQ -> CHAR_SEQ | ( KW_FIX LPAREN ID COMMA INT RPAREN ) -> ^( FIX ID INT ) | ( KW_STAR LPAREN regDefinition RPAREN ) -> ^( STAR regDefinition ) | ( LSQUARE CHAR_LIT MINUS CHAR_LIT RSQUARE ) -> ^( RANGE CHAR_LIT CHAR_LIT ) | ( LSQUARE CHAR_SEQ MINUS CHAR_SEQ RSQUARE ) -> ^( CHARSEQRANGE CHAR_SEQ CHAR_SEQ ) | ( KW_OR LPAREN regDefinition ( COMMA regDefinition )* RPAREN ) -> ^( OR ( regDefinition )+ ) | ( KW_CONCAT LPAREN regDefinition ( COMMA regDefinition )* RPAREN ) -> ^( CONCAT ( regDefinition )+ ) );
    public final HampiParser.regDefinition_return regDefinition() throws RecognitionException {
        HampiParser.regDefinition_return retval = new HampiParser.regDefinition_return();
        retval.start = input.LT(1);

        Object root_0 = null;

        Token ID51=null;
        Token STR_LIT52=null;
        Token CHAR_SEQ53=null;
        Token KW_FIX54=null;
        Token LPAREN55=null;
        Token ID56=null;
        Token COMMA57=null;
        Token INT58=null;
        Token RPAREN59=null;
        Token KW_STAR60=null;
        Token LPAREN61=null;
        Token RPAREN63=null;
        Token LSQUARE64=null;
        Token CHAR_LIT65=null;
        Token MINUS66=null;
        Token CHAR_LIT67=null;
        Token RSQUARE68=null;
        Token LSQUARE69=null;
        Token CHAR_SEQ70=null;
        Token MINUS71=null;
        Token CHAR_SEQ72=null;
        Token RSQUARE73=null;
        Token KW_OR74=null;
        Token LPAREN75=null;
        Token COMMA77=null;
        Token RPAREN79=null;
        Token KW_CONCAT80=null;
        Token LPAREN81=null;
        Token COMMA83=null;
        Token RPAREN85=null;
        HampiParser.regDefinition_return regDefinition62 = null;

        HampiParser.regDefinition_return regDefinition76 = null;

        HampiParser.regDefinition_return regDefinition78 = null;

        HampiParser.regDefinition_return regDefinition82 = null;

        HampiParser.regDefinition_return regDefinition84 = null;


        Object ID51_tree=null;
        Object STR_LIT52_tree=null;
        Object CHAR_SEQ53_tree=null;
        Object KW_FIX54_tree=null;
        Object LPAREN55_tree=null;
        Object ID56_tree=null;
        Object COMMA57_tree=null;
        Object INT58_tree=null;
        Object RPAREN59_tree=null;
        Object KW_STAR60_tree=null;
        Object LPAREN61_tree=null;
        Object RPAREN63_tree=null;
        Object LSQUARE64_tree=null;
        Object CHAR_LIT65_tree=null;
        Object MINUS66_tree=null;
        Object CHAR_LIT67_tree=null;
        Object RSQUARE68_tree=null;
        Object LSQUARE69_tree=null;
        Object CHAR_SEQ70_tree=null;
        Object MINUS71_tree=null;
        Object CHAR_SEQ72_tree=null;
        Object RSQUARE73_tree=null;
        Object KW_OR74_tree=null;
        Object LPAREN75_tree=null;
        Object COMMA77_tree=null;
        Object RPAREN79_tree=null;
        Object KW_CONCAT80_tree=null;
        Object LPAREN81_tree=null;
        Object COMMA83_tree=null;
        Object RPAREN85_tree=null;
        RewriteRuleTokenStream stream_CHAR_SEQ=new RewriteRuleTokenStream(adaptor,"token CHAR_SEQ");
        RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
        RewriteRuleTokenStream stream_KW_FIX=new RewriteRuleTokenStream(adaptor,"token KW_FIX");
        RewriteRuleTokenStream stream_LSQUARE=new RewriteRuleTokenStream(adaptor,"token LSQUARE");
        RewriteRuleTokenStream stream_KW_CONCAT=new RewriteRuleTokenStream(adaptor,"token KW_CONCAT");
        RewriteRuleTokenStream stream_KW_OR=new RewriteRuleTokenStream(adaptor,"token KW_OR");
        RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");
        RewriteRuleTokenStream stream_STR_LIT=new RewriteRuleTokenStream(adaptor,"token STR_LIT");
        RewriteRuleTokenStream stream_INT=new RewriteRuleTokenStream(adaptor,"token INT");
        RewriteRuleTokenStream stream_KW_STAR=new RewriteRuleTokenStream(adaptor,"token KW_STAR");
        RewriteRuleTokenStream stream_CHAR_LIT=new RewriteRuleTokenStream(adaptor,"token CHAR_LIT");
        RewriteRuleTokenStream stream_RSQUARE=new RewriteRuleTokenStream(adaptor,"token RSQUARE");
        RewriteRuleTokenStream stream_MINUS=new RewriteRuleTokenStream(adaptor,"token MINUS");
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
        RewriteRuleSubtreeStream stream_regDefinition=new RewriteRuleSubtreeStream(adaptor,"rule regDefinition");
        try {
            // src/hampi/parser/Hampi.g:82:19: ( ID -> ID | STR_LIT -> STR_LIT | CHAR_SEQ -> CHAR_SEQ | ( KW_FIX LPAREN ID COMMA INT RPAREN ) -> ^( FIX ID INT ) | ( KW_STAR LPAREN regDefinition RPAREN ) -> ^( STAR regDefinition ) | ( LSQUARE CHAR_LIT MINUS CHAR_LIT RSQUARE ) -> ^( RANGE CHAR_LIT CHAR_LIT ) | ( LSQUARE CHAR_SEQ MINUS CHAR_SEQ RSQUARE ) -> ^( CHARSEQRANGE CHAR_SEQ CHAR_SEQ ) | ( KW_OR LPAREN regDefinition ( COMMA regDefinition )* RPAREN ) -> ^( OR ( regDefinition )+ ) | ( KW_CONCAT LPAREN regDefinition ( COMMA regDefinition )* RPAREN ) -> ^( CONCAT ( regDefinition )+ ) )
            int alt8=9;
            alt8 = dfa8.predict(input);
            switch (alt8) {
                case 1 :
                    // src/hampi/parser/Hampi.g:82:21: ID
                    {
                    ID51=(Token)match(input,ID,FOLLOW_ID_in_regDefinition914); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_ID.add(ID51);
                    }



                    // AST REWRITE
                    // elements: ID
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = adaptor.nil();
                    // 82:24: -> ID
                    {
                        adaptor.addChild(root_0, stream_ID.nextNode());

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;
                case 2 :
                    // src/hampi/parser/Hampi.g:83:21: STR_LIT
                    {
                    STR_LIT52=(Token)match(input,STR_LIT,FOLLOW_STR_LIT_in_regDefinition940); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_STR_LIT.add(STR_LIT52);
                    }



                    // AST REWRITE
                    // elements: STR_LIT
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = adaptor.nil();
                    // 83:29: -> STR_LIT
                    {
                        adaptor.addChild(root_0, stream_STR_LIT.nextNode());

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;
                case 3 :
                    // src/hampi/parser/Hampi.g:84:21: CHAR_SEQ
                    {
                    CHAR_SEQ53=(Token)match(input,CHAR_SEQ,FOLLOW_CHAR_SEQ_in_regDefinition966); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_CHAR_SEQ.add(CHAR_SEQ53);
                    }



                    // AST REWRITE
                    // elements: CHAR_SEQ
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = adaptor.nil();
                    // 84:30: -> CHAR_SEQ
                    {
                        adaptor.addChild(root_0, stream_CHAR_SEQ.nextNode());

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;
                case 4 :
                    // src/hampi/parser/Hampi.g:85:21: ( KW_FIX LPAREN ID COMMA INT RPAREN )
                    {
                    // src/hampi/parser/Hampi.g:85:21: ( KW_FIX LPAREN ID COMMA INT RPAREN )
                    // src/hampi/parser/Hampi.g:85:22: KW_FIX LPAREN ID COMMA INT RPAREN
                    {
                    KW_FIX54=(Token)match(input,KW_FIX,FOLLOW_KW_FIX_in_regDefinition994); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_KW_FIX.add(KW_FIX54);
                    }

                    LPAREN55=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_regDefinition996); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_LPAREN.add(LPAREN55);
                    }

                    ID56=(Token)match(input,ID,FOLLOW_ID_in_regDefinition998); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_ID.add(ID56);
                    }

                    COMMA57=(Token)match(input,COMMA,FOLLOW_COMMA_in_regDefinition1000); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_COMMA.add(COMMA57);
                    }

                    INT58=(Token)match(input,INT,FOLLOW_INT_in_regDefinition1002); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_INT.add(INT58);
                    }

                    RPAREN59=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_regDefinition1004); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_RPAREN.add(RPAREN59);
                    }


                    }



                    // AST REWRITE
                    // elements: INT, ID
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = adaptor.nil();
                    // 85:57: -> ^( FIX ID INT )
                    {
                        // src/hampi/parser/Hampi.g:85:60: ^( FIX ID INT )
                        {
                        Object root_1 = adaptor.nil();
                        root_1 = adaptor.becomeRoot(adaptor.create(FIX, "FIX"), root_1);

                        adaptor.addChild(root_1, stream_ID.nextNode());
                        adaptor.addChild(root_1, stream_INT.nextNode());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;
                case 5 :
                    // src/hampi/parser/Hampi.g:86:21: ( KW_STAR LPAREN regDefinition RPAREN )
                    {
                    // src/hampi/parser/Hampi.g:86:21: ( KW_STAR LPAREN regDefinition RPAREN )
                    // src/hampi/parser/Hampi.g:86:22: KW_STAR LPAREN regDefinition RPAREN
                    {
                    KW_STAR60=(Token)match(input,KW_STAR,FOLLOW_KW_STAR_in_regDefinition1038); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_KW_STAR.add(KW_STAR60);
                    }

                    LPAREN61=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_regDefinition1040); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_LPAREN.add(LPAREN61);
                    }

                    pushFollow(FOLLOW_regDefinition_in_regDefinition1042);
                    regDefinition62=regDefinition();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ){
                      stream_regDefinition.add(regDefinition62.getTree());
                    }
                    RPAREN63=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_regDefinition1044); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_RPAREN.add(RPAREN63);
                    }


                    }



                    // AST REWRITE
                    // elements: regDefinition
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = adaptor.nil();
                    // 86:59: -> ^( STAR regDefinition )
                    {
                        // src/hampi/parser/Hampi.g:86:62: ^( STAR regDefinition )
                        {
                        Object root_1 = adaptor.nil();
                        root_1 = adaptor.becomeRoot(adaptor.create(STAR, "STAR"), root_1);

                        adaptor.addChild(root_1, stream_regDefinition.nextTree());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;
                case 6 :
                    // src/hampi/parser/Hampi.g:87:21: ( LSQUARE CHAR_LIT MINUS CHAR_LIT RSQUARE )
                    {
                    // src/hampi/parser/Hampi.g:87:21: ( LSQUARE CHAR_LIT MINUS CHAR_LIT RSQUARE )
                    // src/hampi/parser/Hampi.g:87:22: LSQUARE CHAR_LIT MINUS CHAR_LIT RSQUARE
                    {
                    LSQUARE64=(Token)match(input,LSQUARE,FOLLOW_LSQUARE_in_regDefinition1076); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_LSQUARE.add(LSQUARE64);
                    }

                    CHAR_LIT65=(Token)match(input,CHAR_LIT,FOLLOW_CHAR_LIT_in_regDefinition1078); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_CHAR_LIT.add(CHAR_LIT65);
                    }

                    MINUS66=(Token)match(input,MINUS,FOLLOW_MINUS_in_regDefinition1080); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_MINUS.add(MINUS66);
                    }

                    CHAR_LIT67=(Token)match(input,CHAR_LIT,FOLLOW_CHAR_LIT_in_regDefinition1082); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_CHAR_LIT.add(CHAR_LIT67);
                    }

                    RSQUARE68=(Token)match(input,RSQUARE,FOLLOW_RSQUARE_in_regDefinition1084); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_RSQUARE.add(RSQUARE68);
                    }


                    }



                    // AST REWRITE
                    // elements: CHAR_LIT, CHAR_LIT
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = adaptor.nil();
                    // 87:63: -> ^( RANGE CHAR_LIT CHAR_LIT )
                    {
                        // src/hampi/parser/Hampi.g:87:66: ^( RANGE CHAR_LIT CHAR_LIT )
                        {
                        Object root_1 = adaptor.nil();
                        root_1 = adaptor.becomeRoot(adaptor.create(RANGE, "RANGE"), root_1);

                        adaptor.addChild(root_1, stream_CHAR_LIT.nextNode());
                        adaptor.addChild(root_1, stream_CHAR_LIT.nextNode());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;
                case 7 :
                    // src/hampi/parser/Hampi.g:88:21: ( LSQUARE CHAR_SEQ MINUS CHAR_SEQ RSQUARE )
                    {
                    // src/hampi/parser/Hampi.g:88:21: ( LSQUARE CHAR_SEQ MINUS CHAR_SEQ RSQUARE )
                    // src/hampi/parser/Hampi.g:88:22: LSQUARE CHAR_SEQ MINUS CHAR_SEQ RSQUARE
                    {
                    LSQUARE69=(Token)match(input,LSQUARE,FOLLOW_LSQUARE_in_regDefinition1118); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_LSQUARE.add(LSQUARE69);
                    }

                    CHAR_SEQ70=(Token)match(input,CHAR_SEQ,FOLLOW_CHAR_SEQ_in_regDefinition1120); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_CHAR_SEQ.add(CHAR_SEQ70);
                    }

                    MINUS71=(Token)match(input,MINUS,FOLLOW_MINUS_in_regDefinition1122); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_MINUS.add(MINUS71);
                    }

                    CHAR_SEQ72=(Token)match(input,CHAR_SEQ,FOLLOW_CHAR_SEQ_in_regDefinition1124); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_CHAR_SEQ.add(CHAR_SEQ72);
                    }

                    RSQUARE73=(Token)match(input,RSQUARE,FOLLOW_RSQUARE_in_regDefinition1126); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_RSQUARE.add(RSQUARE73);
                    }


                    }



                    // AST REWRITE
                    // elements: CHAR_SEQ, CHAR_SEQ
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = adaptor.nil();
                    // 88:63: -> ^( CHARSEQRANGE CHAR_SEQ CHAR_SEQ )
                    {
                        // src/hampi/parser/Hampi.g:88:66: ^( CHARSEQRANGE CHAR_SEQ CHAR_SEQ )
                        {
                        Object root_1 = adaptor.nil();
                        root_1 = adaptor.becomeRoot(adaptor.create(CHARSEQRANGE, "CHARSEQRANGE"), root_1);

                        adaptor.addChild(root_1, stream_CHAR_SEQ.nextNode());
                        adaptor.addChild(root_1, stream_CHAR_SEQ.nextNode());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;
                case 8 :
                    // src/hampi/parser/Hampi.g:89:21: ( KW_OR LPAREN regDefinition ( COMMA regDefinition )* RPAREN )
                    {
                    // src/hampi/parser/Hampi.g:89:21: ( KW_OR LPAREN regDefinition ( COMMA regDefinition )* RPAREN )
                    // src/hampi/parser/Hampi.g:89:22: KW_OR LPAREN regDefinition ( COMMA regDefinition )* RPAREN
                    {
                    KW_OR74=(Token)match(input,KW_OR,FOLLOW_KW_OR_in_regDefinition1161); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_KW_OR.add(KW_OR74);
                    }

                    LPAREN75=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_regDefinition1163); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_LPAREN.add(LPAREN75);
                    }

                    pushFollow(FOLLOW_regDefinition_in_regDefinition1165);
                    regDefinition76=regDefinition();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ){
                      stream_regDefinition.add(regDefinition76.getTree());
                    }
                    // src/hampi/parser/Hampi.g:89:49: ( COMMA regDefinition )*
                    loop6:
                    do {
                        int alt6=2;
                        int LA6_0 = input.LA(1);

                        if ( (LA6_0==COMMA) ) {
                            alt6=1;
                        }


                        switch (alt6) {
                    	case 1 :
                    	    // src/hampi/parser/Hampi.g:89:50: COMMA regDefinition
                    	    {
                    	    COMMA77=(Token)match(input,COMMA,FOLLOW_COMMA_in_regDefinition1168); if (state.failed) return retval; 
                    	    if ( state.backtracking==0 ){
                            stream_COMMA.add(COMMA77);
                          }

                    	    pushFollow(FOLLOW_regDefinition_in_regDefinition1170);
                    	    regDefinition78=regDefinition();

                    	    state._fsp--;
                    	    if (state.failed) return retval;
                    	    if ( state.backtracking==0 ){
                            stream_regDefinition.add(regDefinition78.getTree());
                          }

                    	    }
                    	    break;

                    	default :
                    	    break loop6;
                        }
                    } while (true);

                    RPAREN79=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_regDefinition1174); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_RPAREN.add(RPAREN79);
                    }


                    }



                    // AST REWRITE
                    // elements: regDefinition
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = adaptor.nil();
                    // 89:80: -> ^( OR ( regDefinition )+ )
                    {
                        // src/hampi/parser/Hampi.g:89:83: ^( OR ( regDefinition )+ )
                        {
                        Object root_1 = adaptor.nil();
                        root_1 = adaptor.becomeRoot(adaptor.create(OR, "OR"), root_1);

                        if ( !(stream_regDefinition.hasNext()) )
                          throw new RewriteEarlyExitException();
                        while ( stream_regDefinition.hasNext() ) {
                            adaptor.addChild(root_1, stream_regDefinition.nextTree());

                        }
                        stream_regDefinition.reset();

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;
                case 9 :
                    // src/hampi/parser/Hampi.g:90:21: ( KW_CONCAT LPAREN regDefinition ( COMMA regDefinition )* RPAREN )
                    {
                    // src/hampi/parser/Hampi.g:90:21: ( KW_CONCAT LPAREN regDefinition ( COMMA regDefinition )* RPAREN )
                    // src/hampi/parser/Hampi.g:90:22: KW_CONCAT LPAREN regDefinition ( COMMA regDefinition )* RPAREN
                    {
                    KW_CONCAT80=(Token)match(input,KW_CONCAT,FOLLOW_KW_CONCAT_in_regDefinition1207); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_KW_CONCAT.add(KW_CONCAT80);
                    }

                    LPAREN81=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_regDefinition1209); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_LPAREN.add(LPAREN81);
                    }

                    pushFollow(FOLLOW_regDefinition_in_regDefinition1211);
                    regDefinition82=regDefinition();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ){
                      stream_regDefinition.add(regDefinition82.getTree());
                    }
                    // src/hampi/parser/Hampi.g:90:53: ( COMMA regDefinition )*
                    loop7:
                    do {
                        int alt7=2;
                        int LA7_0 = input.LA(1);

                        if ( (LA7_0==COMMA) ) {
                            alt7=1;
                        }


                        switch (alt7) {
                    	case 1 :
                    	    // src/hampi/parser/Hampi.g:90:54: COMMA regDefinition
                    	    {
                    	    COMMA83=(Token)match(input,COMMA,FOLLOW_COMMA_in_regDefinition1214); if (state.failed) return retval; 
                    	    if ( state.backtracking==0 ){
                            stream_COMMA.add(COMMA83);
                          }

                    	    pushFollow(FOLLOW_regDefinition_in_regDefinition1216);
                    	    regDefinition84=regDefinition();

                    	    state._fsp--;
                    	    if (state.failed) return retval;
                    	    if ( state.backtracking==0 ){
                            stream_regDefinition.add(regDefinition84.getTree());
                          }

                    	    }
                    	    break;

                    	default :
                    	    break loop7;
                        }
                    } while (true);

                    RPAREN85=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_regDefinition1220); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_RPAREN.add(RPAREN85);
                    }


                    }



                    // AST REWRITE
                    // elements: regDefinition
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = adaptor.nil();
                    // 90:84: -> ^( CONCAT ( regDefinition )+ )
                    {
                        // src/hampi/parser/Hampi.g:90:87: ^( CONCAT ( regDefinition )+ )
                        {
                        Object root_1 = adaptor.nil();
                        root_1 = adaptor.becomeRoot(adaptor.create(CONCAT, "CONCAT"), root_1);

                        if ( !(stream_regDefinition.hasNext()) )
                          throw new RewriteEarlyExitException();
                        while ( stream_regDefinition.hasNext() ) {
                            adaptor.addChild(root_1, stream_regDefinition.nextTree());

                        }
                        stream_regDefinition.reset();

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( state.backtracking==0 ) {

            retval.tree = adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }
        finally {
        }
        return retval;
    }
    // $ANTLR end regDefinition

    public static class valDeclStmt_return extends ParserRuleReturnScope {
        Object tree;
        @Override
        public Object getTree() { return tree; }
    };

    // $ANTLR start valDeclStmt
    // src/hampi/parser/Hampi.g:93:2: valDeclStmt : ( KW_VAL ID ASSIGN expr ) -> ^( VAL ID expr ) ;
    public final HampiParser.valDeclStmt_return valDeclStmt() throws RecognitionException {
        HampiParser.valDeclStmt_return retval = new HampiParser.valDeclStmt_return();
        retval.start = input.LT(1);

        Object root_0 = null;

        Token KW_VAL86=null;
        Token ID87=null;
        Token ASSIGN88=null;
        HampiParser.expr_return expr89 = null;


        Object KW_VAL86_tree=null;
        Object ID87_tree=null;
        Object ASSIGN88_tree=null;
        RewriteRuleTokenStream stream_KW_VAL=new RewriteRuleTokenStream(adaptor,"token KW_VAL");
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_ASSIGN=new RewriteRuleTokenStream(adaptor,"token ASSIGN");
        RewriteRuleSubtreeStream stream_expr=new RewriteRuleSubtreeStream(adaptor,"rule expr");
        try {
            // src/hampi/parser/Hampi.g:93:14: ( ( KW_VAL ID ASSIGN expr ) -> ^( VAL ID expr ) )
            // src/hampi/parser/Hampi.g:93:16: ( KW_VAL ID ASSIGN expr )
            {
            // src/hampi/parser/Hampi.g:93:16: ( KW_VAL ID ASSIGN expr )
            // src/hampi/parser/Hampi.g:93:17: KW_VAL ID ASSIGN expr
            {
            KW_VAL86=(Token)match(input,KW_VAL,FOLLOW_KW_VAL_in_valDeclStmt1261); if (state.failed) return retval; 
            if ( state.backtracking==0 ){
              stream_KW_VAL.add(KW_VAL86);
            }

            ID87=(Token)match(input,ID,FOLLOW_ID_in_valDeclStmt1263); if (state.failed) return retval; 
            if ( state.backtracking==0 ){
              stream_ID.add(ID87);
            }

            ASSIGN88=(Token)match(input,ASSIGN,FOLLOW_ASSIGN_in_valDeclStmt1265); if (state.failed) return retval; 
            if ( state.backtracking==0 ){
              stream_ASSIGN.add(ASSIGN88);
            }

            pushFollow(FOLLOW_expr_in_valDeclStmt1267);
            expr89=expr();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ){
              stream_expr.add(expr89.getTree());
            }

            }



            // AST REWRITE
            // elements: ID, expr
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( state.backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = adaptor.nil();
            // 93:40: -> ^( VAL ID expr )
            {
                // src/hampi/parser/Hampi.g:93:43: ^( VAL ID expr )
                {
                Object root_1 = adaptor.nil();
                root_1 = adaptor.becomeRoot(adaptor.create(VAL, "VAL"), root_1);

                adaptor.addChild(root_1, stream_ID.nextNode());
                adaptor.addChild(root_1, stream_expr.nextTree());

                adaptor.addChild(root_0, root_1);
                }

            }

            retval.tree = root_0;retval.tree = root_0;}
            }

            retval.stop = input.LT(-1);

            if ( state.backtracking==0 ) {

            retval.tree = adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }
        finally {
        }
        return retval;
    }
    // $ANTLR end valDeclStmt

    public static class expr_return extends ParserRuleReturnScope {
        Object tree;
        @Override
        public Object getTree() { return tree; }
    };

    // $ANTLR start expr
    // src/hampi/parser/Hampi.g:95:2: expr : ( STR_LIT -> STR_LIT | ID -> ID | ( KW_CONCAT LPAREN expr ( COMMA expr )* RPAREN ) -> ^( CONCAT ( expr )+ ) );
    public final HampiParser.expr_return expr() throws RecognitionException {
        HampiParser.expr_return retval = new HampiParser.expr_return();
        retval.start = input.LT(1);

        Object root_0 = null;

        Token STR_LIT90=null;
        Token ID91=null;
        Token KW_CONCAT92=null;
        Token LPAREN93=null;
        Token COMMA95=null;
        Token RPAREN97=null;
        HampiParser.expr_return expr94 = null;

        HampiParser.expr_return expr96 = null;


        Object STR_LIT90_tree=null;
        Object ID91_tree=null;
        Object KW_CONCAT92_tree=null;
        Object LPAREN93_tree=null;
        Object COMMA95_tree=null;
        Object RPAREN97_tree=null;
        RewriteRuleTokenStream stream_RPAREN=new RewriteRuleTokenStream(adaptor,"token RPAREN");
        RewriteRuleTokenStream stream_KW_CONCAT=new RewriteRuleTokenStream(adaptor,"token KW_CONCAT");
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_COMMA=new RewriteRuleTokenStream(adaptor,"token COMMA");
        RewriteRuleTokenStream stream_LPAREN=new RewriteRuleTokenStream(adaptor,"token LPAREN");
        RewriteRuleTokenStream stream_STR_LIT=new RewriteRuleTokenStream(adaptor,"token STR_LIT");
        RewriteRuleSubtreeStream stream_expr=new RewriteRuleSubtreeStream(adaptor,"rule expr");
        try {
            // src/hampi/parser/Hampi.g:95:7: ( STR_LIT -> STR_LIT | ID -> ID | ( KW_CONCAT LPAREN expr ( COMMA expr )* RPAREN ) -> ^( CONCAT ( expr )+ ) )
            int alt10=3;
            switch ( input.LA(1) ) {
            case STR_LIT:
                {
                alt10=1;
                }
                break;
            case ID:
                {
                alt10=2;
                }
                break;
            case KW_CONCAT:
                {
                alt10=3;
                }
                break;
            default:
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 10, 0, input);

                throw nvae;
            }

            switch (alt10) {
                case 1 :
                    // src/hampi/parser/Hampi.g:95:9: STR_LIT
                    {
                    STR_LIT90=(Token)match(input,STR_LIT,FOLLOW_STR_LIT_in_expr1288); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_STR_LIT.add(STR_LIT90);
                    }



                    // AST REWRITE
                    // elements: STR_LIT
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = adaptor.nil();
                    // 95:17: -> STR_LIT
                    {
                        adaptor.addChild(root_0, stream_STR_LIT.nextNode());

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;
                case 2 :
                    // src/hampi/parser/Hampi.g:96:9: ID
                    {
                    ID91=(Token)match(input,ID,FOLLOW_ID_in_expr1302); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_ID.add(ID91);
                    }



                    // AST REWRITE
                    // elements: ID
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = adaptor.nil();
                    // 96:17: -> ID
                    {
                        adaptor.addChild(root_0, stream_ID.nextNode());

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;
                case 3 :
                    // src/hampi/parser/Hampi.g:97:9: ( KW_CONCAT LPAREN expr ( COMMA expr )* RPAREN )
                    {
                    // src/hampi/parser/Hampi.g:97:9: ( KW_CONCAT LPAREN expr ( COMMA expr )* RPAREN )
                    // src/hampi/parser/Hampi.g:97:10: KW_CONCAT LPAREN expr ( COMMA expr )* RPAREN
                    {
                    KW_CONCAT92=(Token)match(input,KW_CONCAT,FOLLOW_KW_CONCAT_in_expr1322); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_KW_CONCAT.add(KW_CONCAT92);
                    }

                    LPAREN93=(Token)match(input,LPAREN,FOLLOW_LPAREN_in_expr1324); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_LPAREN.add(LPAREN93);
                    }

                    pushFollow(FOLLOW_expr_in_expr1326);
                    expr94=expr();

                    state._fsp--;
                    if (state.failed) return retval;
                    if ( state.backtracking==0 ){
                      stream_expr.add(expr94.getTree());
                    }
                    // src/hampi/parser/Hampi.g:97:32: ( COMMA expr )*
                    loop9:
                    do {
                        int alt9=2;
                        int LA9_0 = input.LA(1);

                        if ( (LA9_0==COMMA) ) {
                            alt9=1;
                        }


                        switch (alt9) {
                    	case 1 :
                    	    // src/hampi/parser/Hampi.g:97:33: COMMA expr
                    	    {
                    	    COMMA95=(Token)match(input,COMMA,FOLLOW_COMMA_in_expr1329); if (state.failed) return retval; 
                    	    if ( state.backtracking==0 ){
                            stream_COMMA.add(COMMA95);
                          }

                    	    pushFollow(FOLLOW_expr_in_expr1331);
                    	    expr96=expr();

                    	    state._fsp--;
                    	    if (state.failed) return retval;
                    	    if ( state.backtracking==0 ){
                            stream_expr.add(expr96.getTree());
                          }

                    	    }
                    	    break;

                    	default :
                    	    break loop9;
                        }
                    } while (true);

                    RPAREN97=(Token)match(input,RPAREN,FOLLOW_RPAREN_in_expr1335); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_RPAREN.add(RPAREN97);
                    }


                    }



                    // AST REWRITE
                    // elements: expr
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = adaptor.nil();
                    // 97:54: -> ^( CONCAT ( expr )+ )
                    {
                        // src/hampi/parser/Hampi.g:97:57: ^( CONCAT ( expr )+ )
                        {
                        Object root_1 = adaptor.nil();
                        root_1 = adaptor.becomeRoot(adaptor.create(CONCAT, "CONCAT"), root_1);

                        if ( !(stream_expr.hasNext()) )
                          throw new RewriteEarlyExitException();
                        while ( stream_expr.hasNext() ) {
                            adaptor.addChild(root_1, stream_expr.nextTree());

                        }
                        stream_expr.reset();

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( state.backtracking==0 ) {

            retval.tree = adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }
        finally {
        }
        return retval;
    }
    // $ANTLR end expr

    public static class assertStmt_return extends ParserRuleReturnScope {
        Object tree;
        @Override
        public Object getTree() { return tree; }
    };

    // $ANTLR start assertStmt
    // src/hampi/parser/Hampi.g:99:2: assertStmt : ( KW_ASSERT boolExpr ) -> ^( ASSERT boolExpr ) ;
    public final HampiParser.assertStmt_return assertStmt() throws RecognitionException {
        HampiParser.assertStmt_return retval = new HampiParser.assertStmt_return();
        retval.start = input.LT(1);

        Object root_0 = null;

        Token KW_ASSERT98=null;
        HampiParser.boolExpr_return boolExpr99 = null;


        Object KW_ASSERT98_tree=null;
        RewriteRuleTokenStream stream_KW_ASSERT=new RewriteRuleTokenStream(adaptor,"token KW_ASSERT");
        RewriteRuleSubtreeStream stream_boolExpr=new RewriteRuleSubtreeStream(adaptor,"rule boolExpr");
        try {
            // src/hampi/parser/Hampi.g:99:13: ( ( KW_ASSERT boolExpr ) -> ^( ASSERT boolExpr ) )
            // src/hampi/parser/Hampi.g:99:15: ( KW_ASSERT boolExpr )
            {
            // src/hampi/parser/Hampi.g:99:15: ( KW_ASSERT boolExpr )
            // src/hampi/parser/Hampi.g:99:16: KW_ASSERT boolExpr
            {
            KW_ASSERT98=(Token)match(input,KW_ASSERT,FOLLOW_KW_ASSERT_in_assertStmt1356); if (state.failed) return retval; 
            if ( state.backtracking==0 ){
              stream_KW_ASSERT.add(KW_ASSERT98);
            }

            pushFollow(FOLLOW_boolExpr_in_assertStmt1358);
            boolExpr99=boolExpr();

            state._fsp--;
            if (state.failed) return retval;
            if ( state.backtracking==0 ){
              stream_boolExpr.add(boolExpr99.getTree());
            }

            }



            // AST REWRITE
            // elements: boolExpr
            // token labels: 
            // rule labels: retval
            // token list labels: 
            // rule list labels: 
            if ( state.backtracking==0 ) {
            retval.tree = root_0;
            RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

            root_0 = adaptor.nil();
            // 99:36: -> ^( ASSERT boolExpr )
            {
                // src/hampi/parser/Hampi.g:99:39: ^( ASSERT boolExpr )
                {
                Object root_1 = adaptor.nil();
                root_1 = adaptor.becomeRoot(adaptor.create(ASSERT, "ASSERT"), root_1);

                adaptor.addChild(root_1, stream_boolExpr.nextTree());

                adaptor.addChild(root_0, root_1);
                }

            }

            retval.tree = root_0;retval.tree = root_0;}
            }

            retval.stop = input.LT(-1);

            if ( state.backtracking==0 ) {

            retval.tree = adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }
        finally {
        }
        return retval;
    }
    // $ANTLR end assertStmt

    public static class boolExpr_return extends ParserRuleReturnScope {
        Object tree;
        @Override
        public Object getTree() { return tree; }
    };

    // $ANTLR start boolExpr
    // src/hampi/parser/Hampi.g:101:5: boolExpr : ( ( ID KW_IN ID ) -> ^( IN ID ID ) | ( ID KW_CONTAINS STR_LIT ) -> ^( CONTAINS ID STR_LIT ) | ( ID KW_NOT KW_IN ID ) -> ^( NOTIN ID ID ) | ( ID KW_NOT KW_CONTAINS STR_LIT ) -> ^( NOTCONTAINS ID STR_LIT ) );
    public final HampiParser.boolExpr_return boolExpr() throws RecognitionException {
        HampiParser.boolExpr_return retval = new HampiParser.boolExpr_return();
        retval.start = input.LT(1);

        Object root_0 = null;

        Token ID100=null;
        Token KW_IN101=null;
        Token ID102=null;
        Token ID103=null;
        Token KW_CONTAINS104=null;
        Token STR_LIT105=null;
        Token ID106=null;
        Token KW_NOT107=null;
        Token KW_IN108=null;
        Token ID109=null;
        Token ID110=null;
        Token KW_NOT111=null;
        Token KW_CONTAINS112=null;
        Token STR_LIT113=null;

        Object ID100_tree=null;
        Object KW_IN101_tree=null;
        Object ID102_tree=null;
        Object ID103_tree=null;
        Object KW_CONTAINS104_tree=null;
        Object STR_LIT105_tree=null;
        Object ID106_tree=null;
        Object KW_NOT107_tree=null;
        Object KW_IN108_tree=null;
        Object ID109_tree=null;
        Object ID110_tree=null;
        Object KW_NOT111_tree=null;
        Object KW_CONTAINS112_tree=null;
        Object STR_LIT113_tree=null;
        RewriteRuleTokenStream stream_KW_IN=new RewriteRuleTokenStream(adaptor,"token KW_IN");
        RewriteRuleTokenStream stream_ID=new RewriteRuleTokenStream(adaptor,"token ID");
        RewriteRuleTokenStream stream_KW_CONTAINS=new RewriteRuleTokenStream(adaptor,"token KW_CONTAINS");
        RewriteRuleTokenStream stream_KW_NOT=new RewriteRuleTokenStream(adaptor,"token KW_NOT");
        RewriteRuleTokenStream stream_STR_LIT=new RewriteRuleTokenStream(adaptor,"token STR_LIT");

        try {
            // src/hampi/parser/Hampi.g:101:14: ( ( ID KW_IN ID ) -> ^( IN ID ID ) | ( ID KW_CONTAINS STR_LIT ) -> ^( CONTAINS ID STR_LIT ) | ( ID KW_NOT KW_IN ID ) -> ^( NOTIN ID ID ) | ( ID KW_NOT KW_CONTAINS STR_LIT ) -> ^( NOTCONTAINS ID STR_LIT ) )
            int alt11=4;
            int LA11_0 = input.LA(1);

            if ( (LA11_0==ID) ) {
                switch ( input.LA(2) ) {
                case KW_IN:
                    {
                    alt11=1;
                    }
                    break;
                case KW_CONTAINS:
                    {
                    alt11=2;
                    }
                    break;
                case KW_NOT:
                    {
                    int LA11_4 = input.LA(3);

                    if ( (LA11_4==KW_IN) ) {
                        alt11=3;
                    }
                    else if ( (LA11_4==KW_CONTAINS) ) {
                        alt11=4;
                    }
                    else {
                        if (state.backtracking>0) {state.failed=true; return retval;}
                        NoViableAltException nvae =
                            new NoViableAltException("", 11, 4, input);

                        throw nvae;
                    }
                    }
                    break;
                default:
                    if (state.backtracking>0) {state.failed=true; return retval;}
                    NoViableAltException nvae =
                        new NoViableAltException("", 11, 1, input);

                    throw nvae;
                }

            }
            else {
                if (state.backtracking>0) {state.failed=true; return retval;}
                NoViableAltException nvae =
                    new NoViableAltException("", 11, 0, input);

                throw nvae;
            }
            switch (alt11) {
                case 1 :
                    // src/hampi/parser/Hampi.g:102:16: ( ID KW_IN ID )
                    {
                    // src/hampi/parser/Hampi.g:102:16: ( ID KW_IN ID )
                    // src/hampi/parser/Hampi.g:102:17: ID KW_IN ID
                    {
                    ID100=(Token)match(input,ID,FOLLOW_ID_in_boolExpr1395); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_ID.add(ID100);
                    }

                    KW_IN101=(Token)match(input,KW_IN,FOLLOW_KW_IN_in_boolExpr1397); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_KW_IN.add(KW_IN101);
                    }

                    ID102=(Token)match(input,ID,FOLLOW_ID_in_boolExpr1399); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_ID.add(ID102);
                    }


                    }



                    // AST REWRITE
                    // elements: ID, ID
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = adaptor.nil();
                    // 102:30: -> ^( IN ID ID )
                    {
                        // src/hampi/parser/Hampi.g:102:33: ^( IN ID ID )
                        {
                        Object root_1 = adaptor.nil();
                        root_1 = adaptor.becomeRoot(adaptor.create(IN, "IN"), root_1);

                        adaptor.addChild(root_1, stream_ID.nextNode());
                        adaptor.addChild(root_1, stream_ID.nextNode());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;
                case 2 :
                    // src/hampi/parser/Hampi.g:103:16: ( ID KW_CONTAINS STR_LIT )
                    {
                    // src/hampi/parser/Hampi.g:103:16: ( ID KW_CONTAINS STR_LIT )
                    // src/hampi/parser/Hampi.g:103:17: ID KW_CONTAINS STR_LIT
                    {
                    ID103=(Token)match(input,ID,FOLLOW_ID_in_boolExpr1428); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_ID.add(ID103);
                    }

                    KW_CONTAINS104=(Token)match(input,KW_CONTAINS,FOLLOW_KW_CONTAINS_in_boolExpr1430); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_KW_CONTAINS.add(KW_CONTAINS104);
                    }

                    STR_LIT105=(Token)match(input,STR_LIT,FOLLOW_STR_LIT_in_boolExpr1432); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_STR_LIT.add(STR_LIT105);
                    }


                    }



                    // AST REWRITE
                    // elements: ID, STR_LIT
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = adaptor.nil();
                    // 103:41: -> ^( CONTAINS ID STR_LIT )
                    {
                        // src/hampi/parser/Hampi.g:103:44: ^( CONTAINS ID STR_LIT )
                        {
                        Object root_1 = adaptor.nil();
                        root_1 = adaptor.becomeRoot(adaptor.create(CONTAINS, "CONTAINS"), root_1);

                        adaptor.addChild(root_1, stream_ID.nextNode());
                        adaptor.addChild(root_1, stream_STR_LIT.nextNode());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;
                case 3 :
                    // src/hampi/parser/Hampi.g:104:16: ( ID KW_NOT KW_IN ID )
                    {
                    // src/hampi/parser/Hampi.g:104:16: ( ID KW_NOT KW_IN ID )
                    // src/hampi/parser/Hampi.g:104:17: ID KW_NOT KW_IN ID
                    {
                    ID106=(Token)match(input,ID,FOLLOW_ID_in_boolExpr1461); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_ID.add(ID106);
                    }

                    KW_NOT107=(Token)match(input,KW_NOT,FOLLOW_KW_NOT_in_boolExpr1463); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_KW_NOT.add(KW_NOT107);
                    }

                    KW_IN108=(Token)match(input,KW_IN,FOLLOW_KW_IN_in_boolExpr1465); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_KW_IN.add(KW_IN108);
                    }

                    ID109=(Token)match(input,ID,FOLLOW_ID_in_boolExpr1467); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_ID.add(ID109);
                    }


                    }



                    // AST REWRITE
                    // elements: ID, ID
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = adaptor.nil();
                    // 104:48: -> ^( NOTIN ID ID )
                    {
                        // src/hampi/parser/Hampi.g:104:51: ^( NOTIN ID ID )
                        {
                        Object root_1 = adaptor.nil();
                        root_1 = adaptor.becomeRoot(adaptor.create(NOTIN, "NOTIN"), root_1);

                        adaptor.addChild(root_1, stream_ID.nextNode());
                        adaptor.addChild(root_1, stream_ID.nextNode());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;
                case 4 :
                    // src/hampi/parser/Hampi.g:105:16: ( ID KW_NOT KW_CONTAINS STR_LIT )
                    {
                    // src/hampi/parser/Hampi.g:105:16: ( ID KW_NOT KW_CONTAINS STR_LIT )
                    // src/hampi/parser/Hampi.g:105:17: ID KW_NOT KW_CONTAINS STR_LIT
                    {
                    ID110=(Token)match(input,ID,FOLLOW_ID_in_boolExpr1507); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_ID.add(ID110);
                    }

                    KW_NOT111=(Token)match(input,KW_NOT,FOLLOW_KW_NOT_in_boolExpr1509); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_KW_NOT.add(KW_NOT111);
                    }

                    KW_CONTAINS112=(Token)match(input,KW_CONTAINS,FOLLOW_KW_CONTAINS_in_boolExpr1511); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_KW_CONTAINS.add(KW_CONTAINS112);
                    }

                    STR_LIT113=(Token)match(input,STR_LIT,FOLLOW_STR_LIT_in_boolExpr1513); if (state.failed) return retval; 
                    if ( state.backtracking==0 ){
                      stream_STR_LIT.add(STR_LIT113);
                    }


                    }



                    // AST REWRITE
                    // elements: STR_LIT, ID
                    // token labels: 
                    // rule labels: retval
                    // token list labels: 
                    // rule list labels: 
                    if ( state.backtracking==0 ) {
                    retval.tree = root_0;
                    RewriteRuleSubtreeStream stream_retval=new RewriteRuleSubtreeStream(adaptor,"token retval",retval!=null?retval.tree:null);

                    root_0 = adaptor.nil();
                    // 105:48: -> ^( NOTCONTAINS ID STR_LIT )
                    {
                        // src/hampi/parser/Hampi.g:105:51: ^( NOTCONTAINS ID STR_LIT )
                        {
                        Object root_1 = adaptor.nil();
                        root_1 = adaptor.becomeRoot(adaptor.create(NOTCONTAINS, "NOTCONTAINS"), root_1);

                        adaptor.addChild(root_1, stream_ID.nextNode());
                        adaptor.addChild(root_1, stream_STR_LIT.nextNode());

                        adaptor.addChild(root_0, root_1);
                        }

                    }

                    retval.tree = root_0;retval.tree = root_0;}
                    }
                    break;

            }
            retval.stop = input.LT(-1);

            if ( state.backtracking==0 ) {

            retval.tree = adaptor.rulePostProcessing(root_0);
            adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);
            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
    	retval.tree = adaptor.errorNode(input, retval.start, input.LT(-1), re);

        }
        finally {
        }
        return retval;
    }
    // $ANTLR end boolExpr

    // Delegated rules


    protected DFA5 dfa5 = new DFA5(this);
    protected DFA8 dfa8 = new DFA8(this);
    static final String DFA5_eotS =
        "\14\uffff";
    static final String DFA5_eofS =
        "\14\uffff";
    static final String DFA5_minS =
        "\1\37\2\uffff\1\37\1\52\1\45\2\uffff\1\46\3\uffff";
    static final String DFA5_maxS =
        "\1\56\2\uffff\1\37\1\55\1\45\2\uffff\1\50\3\uffff";
    static final String DFA5_acceptS =
        "\1\uffff\1\1\1\2\3\uffff\1\6\1\7\1\uffff\1\5\1\4\1\3";
    static final String DFA5_specialS =
        "\14\uffff}>";
    static final String[] DFA5_transitionS = {
            "\1\2\4\uffff\1\3\4\uffff\1\4\3\uffff\2\1",
            "",
            "",
            "\1\5",
            "\1\6\2\uffff\1\7",
            "\1\10",
            "",
            "",
            "\1\13\1\12\1\11",
            "",
            "",
            ""
    };

    static final short[] DFA5_eot = DFA.unpackEncodedString(DFA5_eotS);
    static final short[] DFA5_eof = DFA.unpackEncodedString(DFA5_eofS);
    static final char[] DFA5_min = DFA.unpackEncodedStringToUnsignedChars(DFA5_minS);
    static final char[] DFA5_max = DFA.unpackEncodedStringToUnsignedChars(DFA5_maxS);
    static final short[] DFA5_accept = DFA.unpackEncodedString(DFA5_acceptS);
    static final short[] DFA5_special = DFA.unpackEncodedString(DFA5_specialS);
    static final short[][] DFA5_transition;

    static {
        int numStates = DFA5_transitionS.length;
        DFA5_transition = new short[numStates][];
        for (int i=0; i<numStates; i++) {
            DFA5_transition[i] = DFA.unpackEncodedString(DFA5_transitionS[i]);
        }
    }

    class DFA5 extends DFA {

        public DFA5(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 5;
            this.eot = DFA5_eot;
            this.eof = DFA5_eof;
            this.min = DFA5_min;
            this.max = DFA5_max;
            this.accept = DFA5_accept;
            this.special = DFA5_special;
            this.transition = DFA5_transition;
        }
        @Override
        public String getDescription() {
            return "66:2: cfgProductionElement : ( cfgTerminal -> cfgTerminal | cfgNonterminal -> cfgNonterminal | LPAREN cfgNonterminal RPAREN QUESTION -> ^( CFGOPTION cfgNonterminal ) | LPAREN cfgNonterminal RPAREN STAR -> ^( CFGSTAR cfgNonterminal ) | LPAREN cfgNonterminal RPAREN PLUS -> ^( CFGPLUS cfgNonterminal ) | LSQUARE CHAR_LIT MINUS CHAR_LIT RSQUARE -> ^( CFGCHARRANGE CHAR_LIT CHAR_LIT ) | LSQUARE CHAR_SEQ MINUS CHAR_SEQ RSQUARE -> ^( CFGCHARSEQRANGE CHAR_SEQ CHAR_SEQ ) );";
        }
    }
    static final String DFA8_eotS =
        "\13\uffff";
    static final String DFA8_eofS =
        "\13\uffff";
    static final String DFA8_minS =
        "\1\37\5\uffff\1\52\4\uffff";
    static final String DFA8_maxS =
        "\1\64\5\uffff\1\55\4\uffff";
    static final String DFA8_acceptS =
        "\1\uffff\1\1\1\2\1\3\1\4\1\5\1\uffff\1\10\1\11\1\6\1\7";
    static final String DFA8_specialS =
        "\13\uffff}>";
    static final String[] DFA8_transitionS = {
            "\1\1\11\uffff\1\6\3\uffff\1\3\1\2\1\uffff\1\4\1\uffff\1\5\1"+
            "\7\1\10",
            "",
            "",
            "",
            "",
            "",
            "\1\11\2\uffff\1\12",
            "",
            "",
            "",
            ""
    };

    static final short[] DFA8_eot = DFA.unpackEncodedString(DFA8_eotS);
    static final short[] DFA8_eof = DFA.unpackEncodedString(DFA8_eofS);
    static final char[] DFA8_min = DFA.unpackEncodedStringToUnsignedChars(DFA8_minS);
    static final char[] DFA8_max = DFA.unpackEncodedStringToUnsignedChars(DFA8_maxS);
    static final short[] DFA8_accept = DFA.unpackEncodedString(DFA8_acceptS);
    static final short[] DFA8_special = DFA.unpackEncodedString(DFA8_specialS);
    static final short[][] DFA8_transition;

    static {
        int numStates = DFA8_transitionS.length;
        DFA8_transition = new short[numStates][];
        for (int i=0; i<numStates; i++) {
            DFA8_transition[i] = DFA.unpackEncodedString(DFA8_transitionS[i]);
        }
    }

    class DFA8 extends DFA {

        public DFA8(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 8;
            this.eot = DFA8_eot;
            this.eof = DFA8_eof;
            this.min = DFA8_min;
            this.max = DFA8_max;
            this.accept = DFA8_accept;
            this.special = DFA8_special;
            this.transition = DFA8_transition;
        }
        @Override
        public String getDescription() {
            return "82:5: regDefinition : ( ID -> ID | STR_LIT -> STR_LIT | CHAR_SEQ -> CHAR_SEQ | ( KW_FIX LPAREN ID COMMA INT RPAREN ) -> ^( FIX ID INT ) | ( KW_STAR LPAREN regDefinition RPAREN ) -> ^( STAR regDefinition ) | ( LSQUARE CHAR_LIT MINUS CHAR_LIT RSQUARE ) -> ^( RANGE CHAR_LIT CHAR_LIT ) | ( LSQUARE CHAR_SEQ MINUS CHAR_SEQ RSQUARE ) -> ^( CHARSEQRANGE CHAR_SEQ CHAR_SEQ ) | ( KW_OR LPAREN regDefinition ( COMMA regDefinition )* RPAREN ) -> ^( OR ( regDefinition )+ ) | ( KW_CONCAT LPAREN regDefinition ( COMMA regDefinition )* RPAREN ) -> ^( CONCAT ( regDefinition )+ ) );";
        }
    }
 

    public static final BitSet FOLLOW_statement_in_program276 = new BitSet(new long[]{0x0000000020000000L});
    public static final BitSet FOLLOW_SEMI_in_program278 = new BitSet(new long[]{0x0060800440000002L});
    public static final BitSet FOLLOW_vardeclStmt_in_statement299 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_cfgStmt_in_statement315 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_regStmt_in_statement330 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_valDeclStmt_in_statement345 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_assertStmt_in_statement360 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_VAR_in_vardeclStmt393 = new BitSet(new long[]{0x0000000080000000L});
    public static final BitSet FOLLOW_ID_in_vardeclStmt395 = new BitSet(new long[]{0x0000000100000000L});
    public static final BitSet FOLLOW_COLON_in_vardeclStmt397 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_INT_in_vardeclStmt399 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_CFG_in_cfgStmt421 = new BitSet(new long[]{0x0000000080000000L});
    public static final BitSet FOLLOW_cfgProduction_in_cfgStmt423 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_cfgProduction443 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_ASSIGN_in_cfgProduction445 = new BitSet(new long[]{0x0000621880000000L});
    public static final BitSet FOLLOW_cfgProductionSet_in_cfgProduction448 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_cfgProductionElementSet_in_cfgProductionSet472 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_BAR_in_cfgProductionSet475 = new BitSet(new long[]{0x0000621880000000L});
    public static final BitSet FOLLOW_cfgProductionElementSet_in_cfgProductionSet477 = new BitSet(new long[]{0x0000000800000002L});
    public static final BitSet FOLLOW_cfgProductionElement_in_cfgProductionElementSet496 = new BitSet(new long[]{0x0000621080000002L});
    public static final BitSet FOLLOW_cfgTerminal_in_cfgProductionElement519 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_cfgNonterminal_in_cfgProductionElement549 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_LPAREN_in_cfgProductionElement579 = new BitSet(new long[]{0x0000000080000000L});
    public static final BitSet FOLLOW_cfgNonterminal_in_cfgProductionElement581 = new BitSet(new long[]{0x0000002000000000L});
    public static final BitSet FOLLOW_RPAREN_in_cfgProductionElement583 = new BitSet(new long[]{0x0000004000000000L});
    public static final BitSet FOLLOW_QUESTION_in_cfgProductionElement585 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_LPAREN_in_cfgProductionElement619 = new BitSet(new long[]{0x0000000080000000L});
    public static final BitSet FOLLOW_cfgNonterminal_in_cfgProductionElement621 = new BitSet(new long[]{0x0000002000000000L});
    public static final BitSet FOLLOW_RPAREN_in_cfgProductionElement623 = new BitSet(new long[]{0x0000008000000000L});
    public static final BitSet FOLLOW_STAR_in_cfgProductionElement625 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_LPAREN_in_cfgProductionElement667 = new BitSet(new long[]{0x0000000080000000L});
    public static final BitSet FOLLOW_cfgNonterminal_in_cfgProductionElement669 = new BitSet(new long[]{0x0000002000000000L});
    public static final BitSet FOLLOW_RPAREN_in_cfgProductionElement671 = new BitSet(new long[]{0x0000010000000000L});
    public static final BitSet FOLLOW_PLUS_in_cfgProductionElement673 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_LSQUARE_in_cfgProductionElement712 = new BitSet(new long[]{0x0000040000000000L});
    public static final BitSet FOLLOW_CHAR_LIT_in_cfgProductionElement714 = new BitSet(new long[]{0x0000080000000000L});
    public static final BitSet FOLLOW_MINUS_in_cfgProductionElement716 = new BitSet(new long[]{0x0000040000000000L});
    public static final BitSet FOLLOW_CHAR_LIT_in_cfgProductionElement718 = new BitSet(new long[]{0x0000100000000000L});
    public static final BitSet FOLLOW_RSQUARE_in_cfgProductionElement720 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_LSQUARE_in_cfgProductionElement759 = new BitSet(new long[]{0x0000200000000000L});
    public static final BitSet FOLLOW_CHAR_SEQ_in_cfgProductionElement761 = new BitSet(new long[]{0x0000080000000000L});
    public static final BitSet FOLLOW_MINUS_in_cfgProductionElement763 = new BitSet(new long[]{0x0000200000000000L});
    public static final BitSet FOLLOW_CHAR_SEQ_in_cfgProductionElement765 = new BitSet(new long[]{0x0000100000000000L});
    public static final BitSet FOLLOW_RSQUARE_in_cfgProductionElement767 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_set_in_cfgTerminal0 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_cfgNonterminal868 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_REG_in_regStmt885 = new BitSet(new long[]{0x0000000080000000L});
    public static final BitSet FOLLOW_ID_in_regStmt887 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_ASSIGN_in_regStmt889 = new BitSet(new long[]{0x001D620080000000L});
    public static final BitSet FOLLOW_regDefinition_in_regStmt891 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_regDefinition914 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_STR_LIT_in_regDefinition940 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_CHAR_SEQ_in_regDefinition966 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_FIX_in_regDefinition994 = new BitSet(new long[]{0x0000001000000000L});
    public static final BitSet FOLLOW_LPAREN_in_regDefinition996 = new BitSet(new long[]{0x0000000080000000L});
    public static final BitSet FOLLOW_ID_in_regDefinition998 = new BitSet(new long[]{0x0002000000000000L});
    public static final BitSet FOLLOW_COMMA_in_regDefinition1000 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_INT_in_regDefinition1002 = new BitSet(new long[]{0x0000002000000000L});
    public static final BitSet FOLLOW_RPAREN_in_regDefinition1004 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_STAR_in_regDefinition1038 = new BitSet(new long[]{0x0000001000000000L});
    public static final BitSet FOLLOW_LPAREN_in_regDefinition1040 = new BitSet(new long[]{0x001D620080000000L});
    public static final BitSet FOLLOW_regDefinition_in_regDefinition1042 = new BitSet(new long[]{0x0000002000000000L});
    public static final BitSet FOLLOW_RPAREN_in_regDefinition1044 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_LSQUARE_in_regDefinition1076 = new BitSet(new long[]{0x0000040000000000L});
    public static final BitSet FOLLOW_CHAR_LIT_in_regDefinition1078 = new BitSet(new long[]{0x0000080000000000L});
    public static final BitSet FOLLOW_MINUS_in_regDefinition1080 = new BitSet(new long[]{0x0000040000000000L});
    public static final BitSet FOLLOW_CHAR_LIT_in_regDefinition1082 = new BitSet(new long[]{0x0000100000000000L});
    public static final BitSet FOLLOW_RSQUARE_in_regDefinition1084 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_LSQUARE_in_regDefinition1118 = new BitSet(new long[]{0x0000200000000000L});
    public static final BitSet FOLLOW_CHAR_SEQ_in_regDefinition1120 = new BitSet(new long[]{0x0000080000000000L});
    public static final BitSet FOLLOW_MINUS_in_regDefinition1122 = new BitSet(new long[]{0x0000200000000000L});
    public static final BitSet FOLLOW_CHAR_SEQ_in_regDefinition1124 = new BitSet(new long[]{0x0000100000000000L});
    public static final BitSet FOLLOW_RSQUARE_in_regDefinition1126 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_OR_in_regDefinition1161 = new BitSet(new long[]{0x0000001000000000L});
    public static final BitSet FOLLOW_LPAREN_in_regDefinition1163 = new BitSet(new long[]{0x001D620080000000L});
    public static final BitSet FOLLOW_regDefinition_in_regDefinition1165 = new BitSet(new long[]{0x0002002000000000L});
    public static final BitSet FOLLOW_COMMA_in_regDefinition1168 = new BitSet(new long[]{0x001D620080000000L});
    public static final BitSet FOLLOW_regDefinition_in_regDefinition1170 = new BitSet(new long[]{0x0002002000000000L});
    public static final BitSet FOLLOW_RPAREN_in_regDefinition1174 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_CONCAT_in_regDefinition1207 = new BitSet(new long[]{0x0000001000000000L});
    public static final BitSet FOLLOW_LPAREN_in_regDefinition1209 = new BitSet(new long[]{0x001D620080000000L});
    public static final BitSet FOLLOW_regDefinition_in_regDefinition1211 = new BitSet(new long[]{0x0002002000000000L});
    public static final BitSet FOLLOW_COMMA_in_regDefinition1214 = new BitSet(new long[]{0x001D620080000000L});
    public static final BitSet FOLLOW_regDefinition_in_regDefinition1216 = new BitSet(new long[]{0x0002002000000000L});
    public static final BitSet FOLLOW_RPAREN_in_regDefinition1220 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_VAL_in_valDeclStmt1261 = new BitSet(new long[]{0x0000000080000000L});
    public static final BitSet FOLLOW_ID_in_valDeclStmt1263 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_ASSIGN_in_valDeclStmt1265 = new BitSet(new long[]{0x0010400080000000L});
    public static final BitSet FOLLOW_expr_in_valDeclStmt1267 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_STR_LIT_in_expr1288 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_expr1302 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_CONCAT_in_expr1322 = new BitSet(new long[]{0x0000001000000000L});
    public static final BitSet FOLLOW_LPAREN_in_expr1324 = new BitSet(new long[]{0x0010400080000000L});
    public static final BitSet FOLLOW_expr_in_expr1326 = new BitSet(new long[]{0x0002002000000000L});
    public static final BitSet FOLLOW_COMMA_in_expr1329 = new BitSet(new long[]{0x0010400080000000L});
    public static final BitSet FOLLOW_expr_in_expr1331 = new BitSet(new long[]{0x0002002000000000L});
    public static final BitSet FOLLOW_RPAREN_in_expr1335 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_ASSERT_in_assertStmt1356 = new BitSet(new long[]{0x0000000080000000L});
    public static final BitSet FOLLOW_boolExpr_in_assertStmt1358 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_boolExpr1395 = new BitSet(new long[]{0x0080000000000000L});
    public static final BitSet FOLLOW_KW_IN_in_boolExpr1397 = new BitSet(new long[]{0x0000000080000000L});
    public static final BitSet FOLLOW_ID_in_boolExpr1399 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_boolExpr1428 = new BitSet(new long[]{0x0100000000000000L});
    public static final BitSet FOLLOW_KW_CONTAINS_in_boolExpr1430 = new BitSet(new long[]{0x0000400000000000L});
    public static final BitSet FOLLOW_STR_LIT_in_boolExpr1432 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_boolExpr1461 = new BitSet(new long[]{0x0200000000000000L});
    public static final BitSet FOLLOW_KW_NOT_in_boolExpr1463 = new BitSet(new long[]{0x0080000000000000L});
    public static final BitSet FOLLOW_KW_IN_in_boolExpr1465 = new BitSet(new long[]{0x0000000080000000L});
    public static final BitSet FOLLOW_ID_in_boolExpr1467 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_boolExpr1507 = new BitSet(new long[]{0x0200000000000000L});
    public static final BitSet FOLLOW_KW_NOT_in_boolExpr1509 = new BitSet(new long[]{0x0100000000000000L});
    public static final BitSet FOLLOW_KW_CONTAINS_in_boolExpr1511 = new BitSet(new long[]{0x0000400000000000L});
    public static final BitSet FOLLOW_STR_LIT_in_boolExpr1513 = new BitSet(new long[]{0x0000000000000002L});

}