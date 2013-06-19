// $ANTLR 3.1b1 src/hampi/parser/HampiTree.g 2009-01-17 21:59:24

package hampi.parser;


import java.util.*;

import org.antlr.runtime.*;
import org.antlr.runtime.BitSet;
import org.antlr.runtime.tree.*;

public class HampiTree extends TreeParser {
    public static final String[] tokenNames = new String[] {
        "<invalid>", "<EOR>", "<DOWN>", "<UP>", "CFGPROD", "ASSIGN", "PROGRAM", "CFGOPTION", "CFGSTAR", "CFGPLUS", "FIX", "CONTAINS", "IN", "ASSERT", "CONCAT", "VAR", "CFG", "REG", "VAL", "CONST", "RANGE", "CHARSEQRANGE", "OR", "NOTIN", "NOTCONTAINS", "CFGCHARRANGE", "CFGCHARSEQRANGE", "CFGPRODELEMSET", "VALS", "SEMI", "KW_VAR", "ID", "COLON", "INT", "KW_CFG", "BAR", "LPAREN", "RPAREN", "QUESTION", "STAR", "PLUS", "LSQUARE", "CHAR_LIT", "MINUS", "RSQUARE", "CHAR_SEQ", "STR_LIT", "KW_REG", "KW_FIX", "COMMA", "KW_STAR", "KW_OR", "KW_CONCAT", "KW_VAL", "KW_ASSERT", "KW_IN", "KW_CONTAINS", "KW_NOT", "KW_QUERY", "EQUALS", "EscapeSequence", "NEWLINE", "WS", "COMMENT", "LINE_COMMENT"
    };
    public static final int CFGSTAR=8;
    public static final int FIX=10;
    public static final int STAR=39;
    public static final int LSQUARE=41;
    public static final int KW_VAL=53;
    public static final int CFGPROD=4;
    public static final int CONST=19;
    public static final int CONTAINS=11;
    public static final int EQUALS=59;
    public static final int ID=31;
    public static final int CFG=16;
    public static final int EOF=-1;
    public static final int LPAREN=36;
    public static final int KW_VAR=30;
    public static final int VALS=28;
    public static final int RPAREN=37;
    public static final int CHAR_SEQ=45;
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
    public static final int SEMI=29;
    public static final int ASSERT=13;
    public static final int CFGCHARSEQRANGE=26;
    public static final int CFGPLUS=9;
    public static final int COLON=32;
    public static final int WS=62;
    public static final int QUESTION=38;
    public static final int KW_CONCAT=52;
    public static final int NEWLINE=61;
    public static final int KW_OR=51;
    public static final int KW_CONTAINS=56;
    public static final int OR=22;
    public static final int CHARSEQRANGE=21;
    public static final int ASSIGN=5;
    public static final int PROGRAM=6;
    public static final int KW_STAR=50;
    public static final int EscapeSequence=60;
    public static final int BAR=35;
    public static final int KW_CFG=34;
    public static final int KW_NOT=57;
    public static final int NOTIN=23;

    // delegates
    // delegators


        public HampiTree(TreeNodeStream input) {
            this(input, new RecognizerSharedState());
        }
        public HampiTree(TreeNodeStream input, RecognizerSharedState state) {
            super(input, state);
        }
        

    @Override
    public String[] getTokenNames() { return HampiTree.tokenNames; }
    @Override
    public String getGrammarFileName() { return "src/hampi/parser/HampiTree.g"; }



    // $ANTLR start program
    // src/hampi/parser/HampiTree.g:14:1: program returns [HProgram program= new HProgram()] : ^( PROGRAM (stmt= statement )+ ) ;
    public final HProgram program() throws RecognitionException {
        HProgram program =  new HProgram();

        HStatement stmt = null;


        try {
            // src/hampi/parser/HampiTree.g:14:52: ( ^( PROGRAM (stmt= statement )+ ) )
            // src/hampi/parser/HampiTree.g:15:9: ^( PROGRAM (stmt= statement )+ )
            {
            match(input,PROGRAM,FOLLOW_PROGRAM_in_program56); 

            match(input, Token.DOWN, null); 
            // src/hampi/parser/HampiTree.g:16:12: (stmt= statement )+
            int cnt1=0;
            loop1:
            do {
                int alt1=2;
                int LA1_0 = input.LA(1);

                if ( (LA1_0==ASSERT||(LA1_0>=VAR && LA1_0<=VAL)) ) {
                    alt1=1;
                }


                switch (alt1) {
            	case 1 :
            	    // src/hampi/parser/HampiTree.g:16:13: stmt= statement
            	    {
            	    pushFollow(FOLLOW_statement_in_program72);
            	    stmt=statement();

            	    state._fsp--;


            	                 program.add(stmt);
            	               

            	    }
            	    break;

            	default :
            	    if ( cnt1 >= 1 ){
                    break loop1;
                  }
                        EarlyExitException eee =
                            new EarlyExitException(1, input);
                        throw eee;
                }
                cnt1++;
            } while (true);


            match(input, Token.UP, null); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return program;
    }
    // $ANTLR end program


    // $ANTLR start statement
    // src/hampi/parser/HampiTree.g:23:1: statement returns [HStatement s = null] : (i1= vardeclStmt | i2= cfgStmt | i3= regStmt | i4= valDeclStmt | i5= assertStmt ) ;
    public final HStatement statement() throws RecognitionException {
        HStatement s =  null;

        HStatement i1 = null;

        CFGStatement i2 = null;

        HRegDeclStatement i3 = null;

        HValDeclStatement i4 = null;

        HAssertStatement i5 = null;


        try {
            // src/hampi/parser/HampiTree.g:23:40: ( (i1= vardeclStmt | i2= cfgStmt | i3= regStmt | i4= valDeclStmt | i5= assertStmt ) )
            // src/hampi/parser/HampiTree.g:24:16: (i1= vardeclStmt | i2= cfgStmt | i3= regStmt | i4= valDeclStmt | i5= assertStmt )
            {
            // src/hampi/parser/HampiTree.g:24:16: (i1= vardeclStmt | i2= cfgStmt | i3= regStmt | i4= valDeclStmt | i5= assertStmt )
            int alt2=5;
            switch ( input.LA(1) ) {
            case VAR:
                {
                alt2=1;
                }
                break;
            case CFG:
                {
                alt2=2;
                }
                break;
            case REG:
                {
                alt2=3;
                }
                break;
            case VAL:
                {
                alt2=4;
                }
                break;
            case ASSERT:
                {
                alt2=5;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 2, 0, input);

                throw nvae;
            }

            switch (alt2) {
                case 1 :
                    // src/hampi/parser/HampiTree.g:24:18: i1= vardeclStmt
                    {
                    pushFollow(FOLLOW_vardeclStmt_in_statement151);
                    i1=vardeclStmt();

                    state._fsp--;

                    s=i1;

                    }
                    break;
                case 2 :
                    // src/hampi/parser/HampiTree.g:25:18: i2= cfgStmt
                    {
                    pushFollow(FOLLOW_cfgStmt_in_statement174);
                    i2=cfgStmt();

                    state._fsp--;

                    s=i2;

                    }
                    break;
                case 3 :
                    // src/hampi/parser/HampiTree.g:26:18: i3= regStmt
                    {
                    pushFollow(FOLLOW_regStmt_in_statement198);
                    i3=regStmt();

                    state._fsp--;

                    s=i3;

                    }
                    break;
                case 4 :
                    // src/hampi/parser/HampiTree.g:27:18: i4= valDeclStmt
                    {
                    pushFollow(FOLLOW_valDeclStmt_in_statement222);
                    i4=valDeclStmt();

                    state._fsp--;

                    s=i4;

                    }
                    break;
                case 5 :
                    // src/hampi/parser/HampiTree.g:28:18: i5= assertStmt
                    {
                    pushFollow(FOLLOW_assertStmt_in_statement245);
                    i5=assertStmt();

                    state._fsp--;

                    s=i5;

                    }
                    break;

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return s;
    }
    // $ANTLR end statement


    // $ANTLR start vardeclStmt
    // src/hampi/parser/HampiTree.g:32:1: vardeclStmt returns [HStatement s = null] : ^( VAR id= ID size= INT ) ;
    public final HStatement vardeclStmt() throws RecognitionException {
        HStatement s =  null;

        CommonTree id=null;
        CommonTree size=null;

        try {
            // src/hampi/parser/HampiTree.g:32:42: ( ^( VAR id= ID size= INT ) )
            // src/hampi/parser/HampiTree.g:33:1: ^( VAR id= ID size= INT )
            {
            match(input,VAR,FOLLOW_VAR_in_vardeclStmt289); 

            match(input, Token.DOWN, null); 
            id=(CommonTree)match(input,ID,FOLLOW_ID_in_vardeclStmt293); 
            size=(CommonTree)match(input,INT,FOLLOW_INT_in_vardeclStmt303); 

                            s = new HVarDeclStatement(id.getText(), size.getText());
                          

            match(input, Token.UP, null); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return s;
    }
    // $ANTLR end vardeclStmt


    // $ANTLR start cfgStmt
    // src/hampi/parser/HampiTree.g:40:1: cfgStmt returns [CFGStatement s = new CFGStatement()] : ^( CFG ^( CFGPROD id= ID (cfgElemSet= cfgProductionElementSet )+ ) ) ;
    public final CFGStatement cfgStmt() throws RecognitionException {
        CFGStatement s =  new CFGStatement();

        CommonTree id=null;
        List cfgElemSet = null;


        try {
            // src/hampi/parser/HampiTree.g:40:54: ( ^( CFG ^( CFGPROD id= ID (cfgElemSet= cfgProductionElementSet )+ ) ) )
            // src/hampi/parser/HampiTree.g:41:1: ^( CFG ^( CFGPROD id= ID (cfgElemSet= cfgProductionElementSet )+ ) )
            {
            match(input,CFG,FOLLOW_CFG_in_cfgStmt343); 

            match(input, Token.DOWN, null); 
            match(input,CFGPROD,FOLLOW_CFGPROD_in_cfgStmt349); 

            match(input, Token.DOWN, null); 
            id=(CommonTree)match(input,ID,FOLLOW_ID_in_cfgStmt353); 

                  s.setId(id.getText());
                
            // src/hampi/parser/HampiTree.g:47:5: (cfgElemSet= cfgProductionElementSet )+
            int cnt3=0;
            loop3:
            do {
                int alt3=2;
                int LA3_0 = input.LA(1);

                if ( (LA3_0==CFGPRODELEMSET) ) {
                    alt3=1;
                }


                switch (alt3) {
            	case 1 :
            	    // src/hampi/parser/HampiTree.g:47:6: cfgElemSet= cfgProductionElementSet
            	    {
            	    pushFollow(FOLLOW_cfgProductionElementSet_in_cfgStmt369);
            	    cfgElemSet=cfgProductionElementSet();

            	    state._fsp--;


            	          s.appendElementSet(cfgElemSet);
            	        

            	    }
            	    break;

            	default :
            	    if ( cnt3 >= 1 ){
                    break loop3;
                  }
                        EarlyExitException eee =
                            new EarlyExitException(3, input);
                        throw eee;
                }
                cnt3++;
            } while (true);


            match(input, Token.UP, null); 

            match(input, Token.UP, null); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return s;
    }
    // $ANTLR end cfgStmt


    // $ANTLR start cfgProductionElementSet
    // src/hampi/parser/HampiTree.g:54:1: cfgProductionElementSet returns [List list= new ArrayList()] : ^( CFGPRODELEMSET (el= cfgProdElement )* ) ;
    public final List cfgProductionElementSet() throws RecognitionException {
        List list =  new ArrayList();

        CFGProductionElement el = null;


        try {
            // src/hampi/parser/HampiTree.g:54:62: ( ^( CFGPRODELEMSET (el= cfgProdElement )* ) )
            // src/hampi/parser/HampiTree.g:55:2: ^( CFGPRODELEMSET (el= cfgProdElement )* )
            {
            match(input,CFGPRODELEMSET,FOLLOW_CFGPRODELEMSET_in_cfgProductionElementSet399); 

            if ( input.LA(1)==Token.DOWN ) {
                match(input, Token.DOWN, null); 
                // src/hampi/parser/HampiTree.g:56:4: (el= cfgProdElement )*
                loop4:
                do {
                    int alt4=2;
                    int LA4_0 = input.LA(1);

                    if ( ((LA4_0>=CFGOPTION && LA4_0<=CFGPLUS)||(LA4_0>=CFGCHARRANGE && LA4_0<=CFGCHARSEQRANGE)||LA4_0==ID||(LA4_0>=CHAR_SEQ && LA4_0<=STR_LIT)) ) {
                        alt4=1;
                    }


                    switch (alt4) {
                	case 1 :
                	    // src/hampi/parser/HampiTree.g:56:5: el= cfgProdElement
                	    {
                	    pushFollow(FOLLOW_cfgProdElement_in_cfgProductionElementSet408);
                	    el=cfgProdElement();

                	    state._fsp--;


                	         list.add(el);
                	       

                	    }
                	    break;

                	default :
                	    break loop4;
                    }
                } while (true);


                match(input, Token.UP, null); 
            }

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return list;
    }
    // $ANTLR end cfgProductionElementSet


    // $ANTLR start cfgProdElement
    // src/hampi/parser/HampiTree.g:62:1: cfgProdElement returns [CFGProductionElement el = null] : (e1= cfgTerminal | e2= cfgNonterminal | e3= cfgOption | e4= cfgStar | e5= cfgPlus | e6= cfgCharRange | e7= cfgCharSeqRange ) ;
    public final CFGProductionElement cfgProdElement() throws RecognitionException {
        CFGProductionElement el =  null;

        CFGTerminal e1 = null;

        CFGNonterminal e2 = null;

        CFGOption e3 = null;

        CFGStar e4 = null;

        CFGPlus e5 = null;

        CFGCharRange e6 = null;

        CFGCharRange e7 = null;


        try {
            // src/hampi/parser/HampiTree.g:62:56: ( (e1= cfgTerminal | e2= cfgNonterminal | e3= cfgOption | e4= cfgStar | e5= cfgPlus | e6= cfgCharRange | e7= cfgCharSeqRange ) )
            // src/hampi/parser/HampiTree.g:63:3: (e1= cfgTerminal | e2= cfgNonterminal | e3= cfgOption | e4= cfgStar | e5= cfgPlus | e6= cfgCharRange | e7= cfgCharSeqRange )
            {
            // src/hampi/parser/HampiTree.g:63:3: (e1= cfgTerminal | e2= cfgNonterminal | e3= cfgOption | e4= cfgStar | e5= cfgPlus | e6= cfgCharRange | e7= cfgCharSeqRange )
            int alt5=7;
            switch ( input.LA(1) ) {
            case CHAR_SEQ:
            case STR_LIT:
                {
                alt5=1;
                }
                break;
            case ID:
                {
                alt5=2;
                }
                break;
            case CFGOPTION:
                {
                alt5=3;
                }
                break;
            case CFGSTAR:
                {
                alt5=4;
                }
                break;
            case CFGPLUS:
                {
                alt5=5;
                }
                break;
            case CFGCHARRANGE:
                {
                alt5=6;
                }
                break;
            case CFGCHARSEQRANGE:
                {
                alt5=7;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 5, 0, input);

                throw nvae;
            }

            switch (alt5) {
                case 1 :
                    // src/hampi/parser/HampiTree.g:63:5: e1= cfgTerminal
                    {
                    pushFollow(FOLLOW_cfgTerminal_in_cfgProdElement435);
                    e1=cfgTerminal();

                    state._fsp--;

                    el=e1;

                    }
                    break;
                case 2 :
                    // src/hampi/parser/HampiTree.g:64:5: e2= cfgNonterminal
                    {
                    pushFollow(FOLLOW_cfgNonterminal_in_cfgProdElement445);
                    e2=cfgNonterminal();

                    state._fsp--;

                    el=e2;

                    }
                    break;
                case 3 :
                    // src/hampi/parser/HampiTree.g:65:5: e3= cfgOption
                    {
                    pushFollow(FOLLOW_cfgOption_in_cfgProdElement455);
                    e3=cfgOption();

                    state._fsp--;

                    el=e3;

                    }
                    break;
                case 4 :
                    // src/hampi/parser/HampiTree.g:66:5: e4= cfgStar
                    {
                    pushFollow(FOLLOW_cfgStar_in_cfgProdElement465);
                    e4=cfgStar();

                    state._fsp--;

                    el=e4;

                    }
                    break;
                case 5 :
                    // src/hampi/parser/HampiTree.g:67:5: e5= cfgPlus
                    {
                    pushFollow(FOLLOW_cfgPlus_in_cfgProdElement475);
                    e5=cfgPlus();

                    state._fsp--;

                    el=e5;

                    }
                    break;
                case 6 :
                    // src/hampi/parser/HampiTree.g:68:5: e6= cfgCharRange
                    {
                    pushFollow(FOLLOW_cfgCharRange_in_cfgProdElement485);
                    e6=cfgCharRange();

                    state._fsp--;

                    el=e6;

                    }
                    break;
                case 7 :
                    // src/hampi/parser/HampiTree.g:69:5: e7= cfgCharSeqRange
                    {
                    pushFollow(FOLLOW_cfgCharSeqRange_in_cfgProdElement495);
                    e7=cfgCharSeqRange();

                    state._fsp--;

                    el=e7;

                    }
                    break;

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return el;
    }
    // $ANTLR end cfgProdElement


    // $ANTLR start cfgTerminal
    // src/hampi/parser/HampiTree.g:73:1: cfgTerminal returns [CFGTerminal t= null] : (str= STR_LIT | seq= CHAR_SEQ ) ;
    public final CFGTerminal cfgTerminal() throws RecognitionException {
        CFGTerminal t =  null;

        CommonTree str=null;
        CommonTree seq=null;

        try {
            // src/hampi/parser/HampiTree.g:73:43: ( (str= STR_LIT | seq= CHAR_SEQ ) )
            // src/hampi/parser/HampiTree.g:74:3: (str= STR_LIT | seq= CHAR_SEQ )
            {
            // src/hampi/parser/HampiTree.g:74:3: (str= STR_LIT | seq= CHAR_SEQ )
            int alt6=2;
            int LA6_0 = input.LA(1);

            if ( (LA6_0==STR_LIT) ) {
                alt6=1;
            }
            else if ( (LA6_0==CHAR_SEQ) ) {
                alt6=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 6, 0, input);

                throw nvae;
            }
            switch (alt6) {
                case 1 :
                    // src/hampi/parser/HampiTree.g:74:4: str= STR_LIT
                    {
                    str=(CommonTree)match(input,STR_LIT,FOLLOW_STR_LIT_in_cfgTerminal524); 
                     t = new CFGTerminal(str.getText()); 

                    }
                    break;
                case 2 :
                    // src/hampi/parser/HampiTree.g:75:4: seq= CHAR_SEQ
                    {
                    seq=(CommonTree)match(input,CHAR_SEQ,FOLLOW_CHAR_SEQ_in_cfgTerminal534); 
                     int s = Integer.valueOf(seq.getText().substring(1,4)); // PIETER
                                      t = new CFGTerminal("\"" + String.valueOf((char)s) + "\""); 

                    }
                    break;

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return t;
    }
    // $ANTLR end cfgTerminal


    // $ANTLR start cfgNonterminal
    // src/hampi/parser/HampiTree.g:79:1: cfgNonterminal returns [CFGNonterminal t= null] : (id= ID ) ;
    public final CFGNonterminal cfgNonterminal() throws RecognitionException {
        CFGNonterminal t =  null;

        CommonTree id=null;

        try {
            // src/hampi/parser/HampiTree.g:79:49: ( (id= ID ) )
            // src/hampi/parser/HampiTree.g:80:3: (id= ID )
            {
            // src/hampi/parser/HampiTree.g:80:3: (id= ID )
            // src/hampi/parser/HampiTree.g:80:4: id= ID
            {
            id=(CommonTree)match(input,ID,FOLLOW_ID_in_cfgNonterminal559); 

                t = new CFGNonterminal(id.getText());
              

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return t;
    }
    // $ANTLR end cfgNonterminal


    // $ANTLR start cfgOption
    // src/hampi/parser/HampiTree.g:86:1: cfgOption returns [CFGOption t= null] : ^( CFGOPTION el= cfgProdElement ) ;
    public final CFGOption cfgOption() throws RecognitionException {
        CFGOption t =  null;

        CFGProductionElement el = null;


        try {
            // src/hampi/parser/HampiTree.g:86:39: ( ^( CFGOPTION el= cfgProdElement ) )
            // src/hampi/parser/HampiTree.g:87:3: ^( CFGOPTION el= cfgProdElement )
            {
            match(input,CFGOPTION,FOLLOW_CFGOPTION_in_cfgOption582); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_cfgProdElement_in_cfgOption590);
            el=cfgProdElement();

            state._fsp--;


                t = new CFGOption(el);
              

            match(input, Token.UP, null); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return t;
    }
    // $ANTLR end cfgOption


    // $ANTLR start cfgStar
    // src/hampi/parser/HampiTree.g:94:1: cfgStar returns [CFGStar t= null] : ^( CFGSTAR el= cfgProdElement ) ;
    public final CFGStar cfgStar() throws RecognitionException {
        CFGStar t =  null;

        CFGProductionElement el = null;


        try {
            // src/hampi/parser/HampiTree.g:94:35: ( ^( CFGSTAR el= cfgProdElement ) )
            // src/hampi/parser/HampiTree.g:95:3: ^( CFGSTAR el= cfgProdElement )
            {
            match(input,CFGSTAR,FOLLOW_CFGSTAR_in_cfgStar613); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_cfgProdElement_in_cfgStar621);
            el=cfgProdElement();

            state._fsp--;


                t = new CFGStar(el);
              

            match(input, Token.UP, null); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return t;
    }
    // $ANTLR end cfgStar


    // $ANTLR start cfgPlus
    // src/hampi/parser/HampiTree.g:102:1: cfgPlus returns [CFGPlus t= null] : ^( CFGPLUS el= cfgProdElement ) ;
    public final CFGPlus cfgPlus() throws RecognitionException {
        CFGPlus t =  null;

        CFGProductionElement el = null;


        try {
            // src/hampi/parser/HampiTree.g:102:35: ( ^( CFGPLUS el= cfgProdElement ) )
            // src/hampi/parser/HampiTree.g:103:3: ^( CFGPLUS el= cfgProdElement )
            {
            match(input,CFGPLUS,FOLLOW_CFGPLUS_in_cfgPlus644); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_cfgProdElement_in_cfgPlus652);
            el=cfgProdElement();

            state._fsp--;


                t = new CFGPlus(el);
              

            match(input, Token.UP, null); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return t;
    }
    // $ANTLR end cfgPlus


    // $ANTLR start cfgCharRange
    // src/hampi/parser/HampiTree.g:110:1: cfgCharRange returns [CFGCharRange r= null] : ^( CFGCHARRANGE ch1= CHAR_LIT ch2= CHAR_LIT ) ;
    public final CFGCharRange cfgCharRange() throws RecognitionException {
        CFGCharRange r =  null;

        CommonTree ch1=null;
        CommonTree ch2=null;

        try {
            // src/hampi/parser/HampiTree.g:110:44: ( ^( CFGCHARRANGE ch1= CHAR_LIT ch2= CHAR_LIT ) )
            // src/hampi/parser/HampiTree.g:111:1: ^( CFGCHARRANGE ch1= CHAR_LIT ch2= CHAR_LIT )
            {
            match(input,CFGCHARRANGE,FOLLOW_CFGCHARRANGE_in_cfgCharRange674); 

            match(input, Token.DOWN, null); 
            ch1=(CommonTree)match(input,CHAR_LIT,FOLLOW_CHAR_LIT_in_cfgCharRange681); 
            ch2=(CommonTree)match(input,CHAR_LIT,FOLLOW_CHAR_LIT_in_cfgCharRange688); 

                r = new CFGCharRange(ch1.getText(), ch2.getText());
              

            match(input, Token.UP, null); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return r;
    }
    // $ANTLR end cfgCharRange


    // $ANTLR start cfgCharSeqRange
    // src/hampi/parser/HampiTree.g:119:1: cfgCharSeqRange returns [CFGCharRange r= null] : ^( CFGCHARSEQRANGE ch1= CHAR_SEQ ch2= CHAR_SEQ ) ;
    public final CFGCharRange cfgCharSeqRange() throws RecognitionException {
        CFGCharRange r =  null;

        CommonTree ch1=null;
        CommonTree ch2=null;

        try {
            // src/hampi/parser/HampiTree.g:119:47: ( ^( CFGCHARSEQRANGE ch1= CHAR_SEQ ch2= CHAR_SEQ ) )
            // src/hampi/parser/HampiTree.g:120:1: ^( CFGCHARSEQRANGE ch1= CHAR_SEQ ch2= CHAR_SEQ )
            {
            match(input,CFGCHARSEQRANGE,FOLLOW_CFGCHARSEQRANGE_in_cfgCharSeqRange709); 

            match(input, Token.DOWN, null); 
            ch1=(CommonTree)match(input,CHAR_SEQ,FOLLOW_CHAR_SEQ_in_cfgCharSeqRange716); 
            ch2=(CommonTree)match(input,CHAR_SEQ,FOLLOW_CHAR_SEQ_in_cfgCharSeqRange723); 

               int ch1i = Integer.valueOf(ch1.getText().substring(1,4)); 
               int ch2i = Integer.valueOf(ch2.getText().substring(1,4));
               String ch1s = ("'" + String.valueOf((char)ch1i) + "'");
               String ch2s = ("'" + String.valueOf((char)ch2i) + "'");
               r = new CFGCharRange(ch1s, ch2s);
              

            match(input, Token.UP, null); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return r;
    }
    // $ANTLR end cfgCharSeqRange


    // $ANTLR start regStmt
    // src/hampi/parser/HampiTree.g:132:1: regStmt returns [HRegDeclStatement stmt = null] : ^( REG id= ID r= regDefinition ) ;
    public final HRegDeclStatement regStmt() throws RecognitionException {
        HRegDeclStatement stmt =  null;

        CommonTree id=null;
        HRegDefinition r = null;


        try {
            // src/hampi/parser/HampiTree.g:132:49: ( ^( REG id= ID r= regDefinition ) )
            // src/hampi/parser/HampiTree.g:133:2: ^( REG id= ID r= regDefinition )
            {
            match(input,REG,FOLLOW_REG_in_regStmt745); 

            match(input, Token.DOWN, null); 
            id=(CommonTree)match(input,ID,FOLLOW_ID_in_regStmt749); 
            pushFollow(FOLLOW_regDefinition_in_regStmt760);
            r=regDefinition();

            state._fsp--;


                     stmt= new HRegDeclStatement(id.getText(), r);
                  

            match(input, Token.UP, null); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return stmt;
    }
    // $ANTLR end regStmt


    // $ANTLR start regDefinition
    // src/hampi/parser/HampiTree.g:140:1: regDefinition returns [HRegDefinition def= null] : (s= regConst | sprime= regCharSeqConst | id= regVarRef | fix= cfgSizeFix | star= regStar | range= regRange | range= regSeqRange | or= regOr | concat= regConcat ) ;
    public final HRegDefinition regDefinition() throws RecognitionException {
        HRegDefinition def =  null;

        HRegDefinition s = null;

        HRegDefinition sprime = null;

        HRegDefinition id = null;

        HRegDefinition fix = null;

        HRegDefinition star = null;

        HRegDefinition range = null;

        HOrRegexp or = null;

        HConcatRegexp concat = null;


        try {
            // src/hampi/parser/HampiTree.g:140:49: ( (s= regConst | sprime= regCharSeqConst | id= regVarRef | fix= cfgSizeFix | star= regStar | range= regRange | range= regSeqRange | or= regOr | concat= regConcat ) )
            // src/hampi/parser/HampiTree.g:141:4: (s= regConst | sprime= regCharSeqConst | id= regVarRef | fix= cfgSizeFix | star= regStar | range= regRange | range= regSeqRange | or= regOr | concat= regConcat )
            {
            // src/hampi/parser/HampiTree.g:141:4: (s= regConst | sprime= regCharSeqConst | id= regVarRef | fix= cfgSizeFix | star= regStar | range= regRange | range= regSeqRange | or= regOr | concat= regConcat )
            int alt7=9;
            switch ( input.LA(1) ) {
            case STR_LIT:
                {
                alt7=1;
                }
                break;
            case CHAR_SEQ:
                {
                alt7=2;
                }
                break;
            case ID:
                {
                alt7=3;
                }
                break;
            case FIX:
                {
                alt7=4;
                }
                break;
            case STAR:
                {
                alt7=5;
                }
                break;
            case RANGE:
                {
                alt7=6;
                }
                break;
            case CHARSEQRANGE:
                {
                alt7=7;
                }
                break;
            case OR:
                {
                alt7=8;
                }
                break;
            case CONCAT:
                {
                alt7=9;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 7, 0, input);

                throw nvae;
            }

            switch (alt7) {
                case 1 :
                    // src/hampi/parser/HampiTree.g:141:5: s= regConst
                    {
                    pushFollow(FOLLOW_regConst_in_regDefinition789);
                    s=regConst();

                    state._fsp--;

                     def = s;  

                    }
                    break;
                case 2 :
                    // src/hampi/parser/HampiTree.g:142:5: sprime= regCharSeqConst
                    {
                    pushFollow(FOLLOW_regCharSeqConst_in_regDefinition805);
                    sprime=regCharSeqConst();

                    state._fsp--;

                     def = sprime; 

                    }
                    break;
                case 3 :
                    // src/hampi/parser/HampiTree.g:143:5: id= regVarRef
                    {
                    pushFollow(FOLLOW_regVarRef_in_regDefinition816);
                    id=regVarRef();

                    state._fsp--;

                     def = id;

                    }
                    break;
                case 4 :
                    // src/hampi/parser/HampiTree.g:144:5: fix= cfgSizeFix
                    {
                    pushFollow(FOLLOW_cfgSizeFix_in_regDefinition830);
                    fix=cfgSizeFix();

                    state._fsp--;

                     def = fix;

                    }
                    break;
                case 5 :
                    // src/hampi/parser/HampiTree.g:145:5: star= regStar
                    {
                    pushFollow(FOLLOW_regStar_in_regDefinition842);
                    star=regStar();

                    state._fsp--;

                     def = star;

                    }
                    break;
                case 6 :
                    // src/hampi/parser/HampiTree.g:146:5: range= regRange
                    {
                    pushFollow(FOLLOW_regRange_in_regDefinition856);
                    range=regRange();

                    state._fsp--;

                     def = range;

                    }
                    break;
                case 7 :
                    // src/hampi/parser/HampiTree.g:147:5: range= regSeqRange
                    {
                    pushFollow(FOLLOW_regSeqRange_in_regDefinition868);
                    range=regSeqRange();

                    state._fsp--;

                     def = range;

                    }
                    break;
                case 8 :
                    // src/hampi/parser/HampiTree.g:148:5: or= regOr
                    {
                    pushFollow(FOLLOW_regOr_in_regDefinition878);
                    or=regOr();

                    state._fsp--;

                     def = or;

                    }
                    break;
                case 9 :
                    // src/hampi/parser/HampiTree.g:149:5: concat= regConcat
                    {
                    pushFollow(FOLLOW_regConcat_in_regDefinition896);
                    concat=regConcat();

                    state._fsp--;

                     def = concat;

                    }
                    break;

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return def;
    }
    // $ANTLR end regDefinition


    // $ANTLR start regVarRef
    // src/hampi/parser/HampiTree.g:153:1: regVarRef returns [HRegDefinition def= null] : (id= ID ) ;
    public final HRegDefinition regVarRef() throws RecognitionException {
        HRegDefinition def =  null;

        CommonTree id=null;

        try {
            // src/hampi/parser/HampiTree.g:153:45: ( (id= ID ) )
            // src/hampi/parser/HampiTree.g:154:1: (id= ID )
            {
            // src/hampi/parser/HampiTree.g:154:1: (id= ID )
            // src/hampi/parser/HampiTree.g:154:2: id= ID
            {
            id=(CommonTree)match(input,ID,FOLLOW_ID_in_regVarRef918); 

                def = new HRegVarRef(id.getText());
              

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return def;
    }
    // $ANTLR end regVarRef


    // $ANTLR start regOr
    // src/hampi/parser/HampiTree.g:159:1: regOr returns [HOrRegexp def= null] : ^( OR (r= regDefinition )+ ) ;
    public final HOrRegexp regOr() throws RecognitionException {
        HOrRegexp def =  null;

        HRegDefinition r = null;


        try {
            // src/hampi/parser/HampiTree.g:159:36: ( ^( OR (r= regDefinition )+ ) )
            // src/hampi/parser/HampiTree.g:160:1: ^( OR (r= regDefinition )+ )
            {
            match(input,OR,FOLLOW_OR_in_regOr936); 


                 def = new HOrRegexp();
               

            match(input, Token.DOWN, null); 
            // src/hampi/parser/HampiTree.g:164:4: (r= regDefinition )+
            int cnt8=0;
            loop8:
            do {
                int alt8=2;
                int LA8_0 = input.LA(1);

                if ( (LA8_0==FIX||LA8_0==CONCAT||(LA8_0>=RANGE && LA8_0<=OR)||LA8_0==ID||LA8_0==STAR||(LA8_0>=CHAR_SEQ && LA8_0<=STR_LIT)) ) {
                    alt8=1;
                }


                switch (alt8) {
            	case 1 :
            	    // src/hampi/parser/HampiTree.g:164:5: r= regDefinition
            	    {
            	    pushFollow(FOLLOW_regDefinition_in_regOr950);
            	    r=regDefinition();

            	    state._fsp--;


            	          def.add(r);
            	        

            	    }
            	    break;

            	default :
            	    if ( cnt8 >= 1 ){
                    break loop8;
                  }
                        EarlyExitException eee =
                            new EarlyExitException(8, input);
                        throw eee;
                }
                cnt8++;
            } while (true);


            match(input, Token.UP, null); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return def;
    }
    // $ANTLR end regOr


    // $ANTLR start regConcat
    // src/hampi/parser/HampiTree.g:171:1: regConcat returns [HConcatRegexp def= null] : ^( CONCAT (r= regDefinition )+ ) ;
    public final HConcatRegexp regConcat() throws RecognitionException {
        HConcatRegexp def =  null;

        HRegDefinition r = null;


        try {
            // src/hampi/parser/HampiTree.g:171:44: ( ^( CONCAT (r= regDefinition )+ ) )
            // src/hampi/parser/HampiTree.g:172:1: ^( CONCAT (r= regDefinition )+ )
            {
            match(input,CONCAT,FOLLOW_CONCAT_in_regConcat978); 


                 def = new HConcatRegexp();
               

            match(input, Token.DOWN, null); 
            // src/hampi/parser/HampiTree.g:176:4: (r= regDefinition )+
            int cnt9=0;
            loop9:
            do {
                int alt9=2;
                int LA9_0 = input.LA(1);

                if ( (LA9_0==FIX||LA9_0==CONCAT||(LA9_0>=RANGE && LA9_0<=OR)||LA9_0==ID||LA9_0==STAR||(LA9_0>=CHAR_SEQ && LA9_0<=STR_LIT)) ) {
                    alt9=1;
                }


                switch (alt9) {
            	case 1 :
            	    // src/hampi/parser/HampiTree.g:176:5: r= regDefinition
            	    {
            	    pushFollow(FOLLOW_regDefinition_in_regConcat992);
            	    r=regDefinition();

            	    state._fsp--;


            	          def.add(r);
            	        

            	    }
            	    break;

            	default :
            	    if ( cnt9 >= 1 ){
                    break loop9;
                  }
                        EarlyExitException eee =
                            new EarlyExitException(9, input);
                        throw eee;
                }
                cnt9++;
            } while (true);


            match(input, Token.UP, null); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return def;
    }
    // $ANTLR end regConcat


    // $ANTLR start regRange
    // src/hampi/parser/HampiTree.g:183:1: regRange returns [HRegDefinition def= null] : ^( RANGE low= CHAR_LIT high= CHAR_LIT ) ;
    public final HRegDefinition regRange() throws RecognitionException {
        HRegDefinition def =  null;

        CommonTree low=null;
        CommonTree high=null;

        try {
            // src/hampi/parser/HampiTree.g:183:44: ( ^( RANGE low= CHAR_LIT high= CHAR_LIT ) )
            // src/hampi/parser/HampiTree.g:184:2: ^( RANGE low= CHAR_LIT high= CHAR_LIT )
            {
            match(input,RANGE,FOLLOW_RANGE_in_regRange1021); 

            match(input, Token.DOWN, null); 
            low=(CommonTree)match(input,CHAR_LIT,FOLLOW_CHAR_LIT_in_regRange1025); 
            high=(CommonTree)match(input,CHAR_LIT,FOLLOW_CHAR_LIT_in_regRange1039); 

                       def = new HRangeRegexp(low.getText(), high.getText());
                     

            match(input, Token.UP, null); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return def;
    }
    // $ANTLR end regRange


    // $ANTLR start regSeqRange
    // src/hampi/parser/HampiTree.g:191:1: regSeqRange returns [HRegDefinition def= null] : ^( CHARSEQRANGE ch1= CHAR_SEQ ch2= CHAR_SEQ ) ;
    public final HRegDefinition regSeqRange() throws RecognitionException {
        HRegDefinition def =  null;

        CommonTree ch1=null;
        CommonTree ch2=null;

        try {
            // src/hampi/parser/HampiTree.g:191:47: ( ^( CHARSEQRANGE ch1= CHAR_SEQ ch2= CHAR_SEQ ) )
            // src/hampi/parser/HampiTree.g:192:2: ^( CHARSEQRANGE ch1= CHAR_SEQ ch2= CHAR_SEQ )
            {
            match(input,CHARSEQRANGE,FOLLOW_CHARSEQRANGE_in_regSeqRange1076); 

            match(input, Token.DOWN, null); 
            ch1=(CommonTree)match(input,CHAR_SEQ,FOLLOW_CHAR_SEQ_in_regSeqRange1080); 
            ch2=(CommonTree)match(input,CHAR_SEQ,FOLLOW_CHAR_SEQ_in_regSeqRange1093); 

                       int ch1i = Integer.valueOf(ch1.getText().substring(1,4));
                       int ch2i = Integer.valueOf(ch2.getText().substring(1,4));
                       String ch1s = ("'" + String.valueOf((char)ch1i) + "'");
                       String ch2s = ("'" + String.valueOf((char)ch2i) + "'");
                       def = new HRangeRegexp(ch1s, ch2s);
                     

            match(input, Token.UP, null); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return def;
    }
    // $ANTLR end regSeqRange


    // $ANTLR start regStar
    // src/hampi/parser/HampiTree.g:203:1: regStar returns [HRegDefinition def= null] : ^( STAR r= regDefinition ) ;
    public final HRegDefinition regStar() throws RecognitionException {
        HRegDefinition def =  null;

        HRegDefinition r = null;


        try {
            // src/hampi/parser/HampiTree.g:203:43: ( ^( STAR r= regDefinition ) )
            // src/hampi/parser/HampiTree.g:204:2: ^( STAR r= regDefinition )
            {
            match(input,STAR,FOLLOW_STAR_in_regStar1129); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_regDefinition_in_regStar1133);
            r=regDefinition();

            state._fsp--;


                  def = new HStarRegexp(r);
                

            match(input, Token.UP, null); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return def;
    }
    // $ANTLR end regStar


    // $ANTLR start regConst
    // src/hampi/parser/HampiTree.g:209:1: regConst returns [HRegDefinition def= null] : (s= STR_LIT ) ;
    public final HRegDefinition regConst() throws RecognitionException {
        HRegDefinition def =  null;

        CommonTree s=null;

        try {
            // src/hampi/parser/HampiTree.g:209:44: ( (s= STR_LIT ) )
            // src/hampi/parser/HampiTree.g:210:2: (s= STR_LIT )
            {
            // src/hampi/parser/HampiTree.g:210:2: (s= STR_LIT )
            // src/hampi/parser/HampiTree.g:210:3: s= STR_LIT
            {
            s=(CommonTree)match(input,STR_LIT,FOLLOW_STR_LIT_in_regConst1156); 

                 def = new HConstRegexp(s.getText());
               

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return def;
    }
    // $ANTLR end regConst


    // $ANTLR start regCharSeqConst
    // src/hampi/parser/HampiTree.g:215:1: regCharSeqConst returns [HRegDefinition def= null] : (s= CHAR_SEQ ) ;
    public final HRegDefinition regCharSeqConst() throws RecognitionException {
        HRegDefinition def =  null;

        CommonTree s=null;

        try {
            // src/hampi/parser/HampiTree.g:215:51: ( (s= CHAR_SEQ ) )
            // src/hampi/parser/HampiTree.g:216:2: (s= CHAR_SEQ )
            {
            // src/hampi/parser/HampiTree.g:216:2: (s= CHAR_SEQ )
            // src/hampi/parser/HampiTree.g:216:3: s= CHAR_SEQ
            {
            s=(CommonTree)match(input,CHAR_SEQ,FOLLOW_CHAR_SEQ_in_regCharSeqConst1179); 

                 int si = Integer.valueOf(s.getText().substring(1,4)); 
                 def = new HConstRegexp("\"" + String.valueOf((char)si) + "\"");
               

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return def;
    }
    // $ANTLR end regCharSeqConst


    // $ANTLR start cfgSizeFix
    // src/hampi/parser/HampiTree.g:222:1: cfgSizeFix returns [HRegDefinition def = null] : ^( FIX id= ID s= INT ) ;
    public final HRegDefinition cfgSizeFix() throws RecognitionException {
        HRegDefinition def =  null;

        CommonTree id=null;
        CommonTree s=null;

        try {
            // src/hampi/parser/HampiTree.g:222:48: ( ^( FIX id= ID s= INT ) )
            // src/hampi/parser/HampiTree.g:223:3: ^( FIX id= ID s= INT )
            {
            match(input,FIX,FOLLOW_FIX_in_cfgSizeFix1202); 

            match(input, Token.DOWN, null); 
            id=(CommonTree)match(input,ID,FOLLOW_ID_in_cfgSizeFix1213); 
            s=(CommonTree)match(input,INT,FOLLOW_INT_in_cfgSizeFix1223); 

                   def = new HSizeFixRegDefinition(id.getText(), s.getText());
                 

            match(input, Token.UP, null); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return def;
    }
    // $ANTLR end cfgSizeFix


    // $ANTLR start valDeclStmt
    // src/hampi/parser/HampiTree.g:231:1: valDeclStmt returns [HValDeclStatement s = null] : ^( VAL id= ID e= expr ) ;
    public final HValDeclStatement valDeclStmt() throws RecognitionException {
        HValDeclStatement s =  null;

        CommonTree id=null;
        HExpression e = null;


        try {
            // src/hampi/parser/HampiTree.g:231:50: ( ^( VAL id= ID e= expr ) )
            // src/hampi/parser/HampiTree.g:232:2: ^( VAL id= ID e= expr )
            {
            match(input,VAL,FOLLOW_VAL_in_valDeclStmt1249); 

            match(input, Token.DOWN, null); 
            id=(CommonTree)match(input,ID,FOLLOW_ID_in_valDeclStmt1256); 
            pushFollow(FOLLOW_expr_in_valDeclStmt1262);
            e=expr();

            state._fsp--;


                s= new HValDeclStatement(id.getText(), e);
              

            match(input, Token.UP, null); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return s;
    }
    // $ANTLR end valDeclStmt


    // $ANTLR start expr
    // src/hampi/parser/HampiTree.g:240:1: expr returns [HExpression e = null] : ( (s= STR_LIT ) | (id= ID ) | ^( CONCAT (sube= expr )+ ) );
    public final HExpression expr() throws RecognitionException {
        HExpression e =  null;

        CommonTree s=null;
        CommonTree id=null;
        HExpression sube = null;


        try {
            // src/hampi/parser/HampiTree.g:240:37: ( (s= STR_LIT ) | (id= ID ) | ^( CONCAT (sube= expr )+ ) )
            int alt11=3;
            switch ( input.LA(1) ) {
            case STR_LIT:
                {
                alt11=1;
                }
                break;
            case ID:
                {
                alt11=2;
                }
                break;
            case CONCAT:
                {
                alt11=3;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 11, 0, input);

                throw nvae;
            }

            switch (alt11) {
                case 1 :
                    // src/hampi/parser/HampiTree.g:241:2: (s= STR_LIT )
                    {
                    // src/hampi/parser/HampiTree.g:241:2: (s= STR_LIT )
                    // src/hampi/parser/HampiTree.g:241:3: s= STR_LIT
                    {
                    s=(CommonTree)match(input,STR_LIT,FOLLOW_STR_LIT_in_expr1288); 

                        e = new HConstantExpression(s.getText());
                      

                    }


                    }
                    break;
                case 2 :
                    // src/hampi/parser/HampiTree.g:247:2: (id= ID )
                    {
                    // src/hampi/parser/HampiTree.g:247:2: (id= ID )
                    // src/hampi/parser/HampiTree.g:247:3: id= ID
                    {
                    id=(CommonTree)match(input,ID,FOLLOW_ID_in_expr1304); 

                       e = new HVarReferenceExpression(id.getText());
                     

                    }


                    }
                    break;
                case 3 :
                    // src/hampi/parser/HampiTree.g:253:2: ^( CONCAT (sube= expr )+ )
                    {
                    match(input,CONCAT,FOLLOW_CONCAT_in_expr1319); 


                          HConcatExpression cat = new HConcatExpression();
                        

                    match(input, Token.DOWN, null); 
                    // src/hampi/parser/HampiTree.g:257:4: (sube= expr )+
                    int cnt10=0;
                    loop10:
                    do {
                        int alt10=2;
                        int LA10_0 = input.LA(1);

                        if ( (LA10_0==CONCAT||LA10_0==ID||LA10_0==STR_LIT) ) {
                            alt10=1;
                        }


                        switch (alt10) {
                    	case 1 :
                    	    // src/hampi/parser/HampiTree.g:257:5: sube= expr
                    	    {
                    	    pushFollow(FOLLOW_expr_in_expr1334);
                    	    sube=expr();

                    	    state._fsp--;


                    	         cat.add(sube);
                    	       

                    	    }
                    	    break;

                    	default :
                    	    if ( cnt10 >= 1 ){
                            break loop10;
                          }
                                EarlyExitException eee =
                                    new EarlyExitException(10, input);
                                throw eee;
                        }
                        cnt10++;
                    } while (true);


                         e = cat;
                       

                    match(input, Token.UP, null); 

                    }
                    break;

            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return e;
    }
    // $ANTLR end expr


    // $ANTLR start assertStmt
    // src/hampi/parser/HampiTree.g:268:1: assertStmt returns [HAssertStatement s= null] : ^( ASSERT b= boolExpr ) ;
    public final HAssertStatement assertStmt() throws RecognitionException {
        HAssertStatement s =  null;

        HBooleanExpression b = null;


        try {
            // src/hampi/parser/HampiTree.g:268:47: ( ^( ASSERT b= boolExpr ) )
            // src/hampi/parser/HampiTree.g:269:2: ^( ASSERT b= boolExpr )
            {
            match(input,ASSERT,FOLLOW_ASSERT_in_assertStmt1371); 

            match(input, Token.DOWN, null); 
            pushFollow(FOLLOW_boolExpr_in_assertStmt1375);
            b=boolExpr();

            state._fsp--;


                 s = new HAssertStatement(b);
               

            match(input, Token.UP, null); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return s;
    }
    // $ANTLR end assertStmt


    // $ANTLR start boolExpr
    // src/hampi/parser/HampiTree.g:276:1: boolExpr returns [HBooleanExpression b = null] : ( ^( IN id1= ID id2= ID ) | ^( CONTAINS id= ID str= STR_LIT ) | ^( NOTIN id1= ID id2= ID ) | ^( NOTCONTAINS id= ID str= STR_LIT ) );
    public final HBooleanExpression boolExpr() throws RecognitionException {
        HBooleanExpression b =  null;

        CommonTree id1=null;
        CommonTree id2=null;
        CommonTree id=null;
        CommonTree str=null;

        try {
            // src/hampi/parser/HampiTree.g:276:48: ( ^( IN id1= ID id2= ID ) | ^( CONTAINS id= ID str= STR_LIT ) | ^( NOTIN id1= ID id2= ID ) | ^( NOTCONTAINS id= ID str= STR_LIT ) )
            int alt12=4;
            switch ( input.LA(1) ) {
            case IN:
                {
                alt12=1;
                }
                break;
            case CONTAINS:
                {
                alt12=2;
                }
                break;
            case NOTIN:
                {
                alt12=3;
                }
                break;
            case NOTCONTAINS:
                {
                alt12=4;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 12, 0, input);

                throw nvae;
            }

            switch (alt12) {
                case 1 :
                    // src/hampi/parser/HampiTree.g:277:5: ^( IN id1= ID id2= ID )
                    {
                    match(input,IN,FOLLOW_IN_in_boolExpr1403); 

                    match(input, Token.DOWN, null); 
                    id1=(CommonTree)match(input,ID,FOLLOW_ID_in_boolExpr1407); 
                    id2=(CommonTree)match(input,ID,FOLLOW_ID_in_boolExpr1411); 

                          b = new HInExpression(id1.getText(), id2.getText(), true);
                        

                    match(input, Token.UP, null); 

                    }
                    break;
                case 2 :
                    // src/hampi/parser/HampiTree.g:282:5: ^( CONTAINS id= ID str= STR_LIT )
                    {
                    match(input,CONTAINS,FOLLOW_CONTAINS_in_boolExpr1430); 

                    match(input, Token.DOWN, null); 
                    id=(CommonTree)match(input,ID,FOLLOW_ID_in_boolExpr1434); 
                    str=(CommonTree)match(input,STR_LIT,FOLLOW_STR_LIT_in_boolExpr1438); 

                          b = new HContainsExpression(id.getText(), str.getText(), true);
                      

                    match(input, Token.UP, null); 

                    }
                    break;
                case 3 :
                    // src/hampi/parser/HampiTree.g:288:5: ^( NOTIN id1= ID id2= ID )
                    {
                    match(input,NOTIN,FOLLOW_NOTIN_in_boolExpr1457); 

                    match(input, Token.DOWN, null); 
                    id1=(CommonTree)match(input,ID,FOLLOW_ID_in_boolExpr1461); 
                    id2=(CommonTree)match(input,ID,FOLLOW_ID_in_boolExpr1465); 

                          b = new HInExpression(id1.getText(), id2.getText(), false);
                        

                    match(input, Token.UP, null); 

                    }
                    break;
                case 4 :
                    // src/hampi/parser/HampiTree.g:293:5: ^( NOTCONTAINS id= ID str= STR_LIT )
                    {
                    match(input,NOTCONTAINS,FOLLOW_NOTCONTAINS_in_boolExpr1484); 

                    match(input, Token.DOWN, null); 
                    id=(CommonTree)match(input,ID,FOLLOW_ID_in_boolExpr1488); 
                    str=(CommonTree)match(input,STR_LIT,FOLLOW_STR_LIT_in_boolExpr1492); 

                          b = new HContainsExpression(id.getText(), str.getText(), false);
                      

                    match(input, Token.UP, null); 

                    }
                    break;

            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return b;
    }
    // $ANTLR end boolExpr

    // Delegated rules


 

    public static final BitSet FOLLOW_PROGRAM_in_program56 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_statement_in_program72 = new BitSet(new long[]{0x000000000007A008L});
    public static final BitSet FOLLOW_vardeclStmt_in_statement151 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_cfgStmt_in_statement174 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_regStmt_in_statement198 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_valDeclStmt_in_statement222 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_assertStmt_in_statement245 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_VAR_in_vardeclStmt289 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_ID_in_vardeclStmt293 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_INT_in_vardeclStmt303 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CFG_in_cfgStmt343 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_CFGPROD_in_cfgStmt349 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_ID_in_cfgStmt353 = new BitSet(new long[]{0x0000000008000000L});
    public static final BitSet FOLLOW_cfgProductionElementSet_in_cfgStmt369 = new BitSet(new long[]{0x0000000008000008L});
    public static final BitSet FOLLOW_CFGPRODELEMSET_in_cfgProductionElementSet399 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_cfgProdElement_in_cfgProductionElementSet408 = new BitSet(new long[]{0x0000600086000388L});
    public static final BitSet FOLLOW_cfgTerminal_in_cfgProdElement435 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_cfgNonterminal_in_cfgProdElement445 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_cfgOption_in_cfgProdElement455 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_cfgStar_in_cfgProdElement465 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_cfgPlus_in_cfgProdElement475 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_cfgCharRange_in_cfgProdElement485 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_cfgCharSeqRange_in_cfgProdElement495 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_STR_LIT_in_cfgTerminal524 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_CHAR_SEQ_in_cfgTerminal534 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_cfgNonterminal559 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_CFGOPTION_in_cfgOption582 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_cfgProdElement_in_cfgOption590 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CFGSTAR_in_cfgStar613 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_cfgProdElement_in_cfgStar621 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CFGPLUS_in_cfgPlus644 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_cfgProdElement_in_cfgPlus652 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CFGCHARRANGE_in_cfgCharRange674 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_CHAR_LIT_in_cfgCharRange681 = new BitSet(new long[]{0x0000040000000000L});
    public static final BitSet FOLLOW_CHAR_LIT_in_cfgCharRange688 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CFGCHARSEQRANGE_in_cfgCharSeqRange709 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_CHAR_SEQ_in_cfgCharSeqRange716 = new BitSet(new long[]{0x0000200000000000L});
    public static final BitSet FOLLOW_CHAR_SEQ_in_cfgCharSeqRange723 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_REG_in_regStmt745 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_ID_in_regStmt749 = new BitSet(new long[]{0x0000608080704400L});
    public static final BitSet FOLLOW_regDefinition_in_regStmt760 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_regConst_in_regDefinition789 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_regCharSeqConst_in_regDefinition805 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_regVarRef_in_regDefinition816 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_cfgSizeFix_in_regDefinition830 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_regStar_in_regDefinition842 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_regRange_in_regDefinition856 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_regSeqRange_in_regDefinition868 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_regOr_in_regDefinition878 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_regConcat_in_regDefinition896 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_regVarRef918 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_OR_in_regOr936 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_regDefinition_in_regOr950 = new BitSet(new long[]{0x0000608080704408L});
    public static final BitSet FOLLOW_CONCAT_in_regConcat978 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_regDefinition_in_regConcat992 = new BitSet(new long[]{0x0000608080704408L});
    public static final BitSet FOLLOW_RANGE_in_regRange1021 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_CHAR_LIT_in_regRange1025 = new BitSet(new long[]{0x0000040000000000L});
    public static final BitSet FOLLOW_CHAR_LIT_in_regRange1039 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CHARSEQRANGE_in_regSeqRange1076 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_CHAR_SEQ_in_regSeqRange1080 = new BitSet(new long[]{0x0000200000000000L});
    public static final BitSet FOLLOW_CHAR_SEQ_in_regSeqRange1093 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_STAR_in_regStar1129 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_regDefinition_in_regStar1133 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_STR_LIT_in_regConst1156 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_CHAR_SEQ_in_regCharSeqConst1179 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_FIX_in_cfgSizeFix1202 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_ID_in_cfgSizeFix1213 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_INT_in_cfgSizeFix1223 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_VAL_in_valDeclStmt1249 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_ID_in_valDeclStmt1256 = new BitSet(new long[]{0x0000400080004000L});
    public static final BitSet FOLLOW_expr_in_valDeclStmt1262 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_STR_LIT_in_expr1288 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_expr1304 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_CONCAT_in_expr1319 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_expr_in_expr1334 = new BitSet(new long[]{0x0000400080004008L});
    public static final BitSet FOLLOW_ASSERT_in_assertStmt1371 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_boolExpr_in_assertStmt1375 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_IN_in_boolExpr1403 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_ID_in_boolExpr1407 = new BitSet(new long[]{0x0000000080000000L});
    public static final BitSet FOLLOW_ID_in_boolExpr1411 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_CONTAINS_in_boolExpr1430 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_ID_in_boolExpr1434 = new BitSet(new long[]{0x0000400000000000L});
    public static final BitSet FOLLOW_STR_LIT_in_boolExpr1438 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_NOTIN_in_boolExpr1457 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_ID_in_boolExpr1461 = new BitSet(new long[]{0x0000000080000000L});
    public static final BitSet FOLLOW_ID_in_boolExpr1465 = new BitSet(new long[]{0x0000000000000008L});
    public static final BitSet FOLLOW_NOTCONTAINS_in_boolExpr1484 = new BitSet(new long[]{0x0000000000000004L});
    public static final BitSet FOLLOW_ID_in_boolExpr1488 = new BitSet(new long[]{0x0000400000000000L});
    public static final BitSet FOLLOW_STR_LIT_in_boolExpr1492 = new BitSet(new long[]{0x0000000000000008L});

}