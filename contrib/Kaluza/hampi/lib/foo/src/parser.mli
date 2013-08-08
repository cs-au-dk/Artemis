type token =
    Colon
  | Semicolon
  | Quotes
  | Name
  | String of string
  | Terminal of string
  | EOF
val yytransl_const : int array
val yytransl_block : int array
val yylhs : string
val yylen : string
val yydefred : string
val yydgoto : string
val yysindex : string
val yyrindex : string
val yygindex : string
val yytablesize : int
val yytable : string
val yycheck : string
val yynames_const : string
val yynames_block : string
val yyact : (Parsing.parser_env -> Obj.t) array
val yytables : Parsing.parse_tables
val cfg : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> Cfg.pureCFG
