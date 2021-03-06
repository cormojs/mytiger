type svalue = Tokens.svalue
type pos = int
type ('a, 'b) token = ('a, 'b) Tokens.token
type lexresult = (svalue, pos) token

val lineNum = ErrorMsg.lineNum
val linePos = ErrorMsg.linePos

val commentLv = ref 0

val strToken = ref ""
val strPos   = ref 0

fun err(p1,p2) = ErrorMsg.error p1

fun eof() = let val pos = hd(!linePos) in Tokens.EOF(pos,pos) end


%% 
%header (functor TigerLexFun (structure Tokens: Tiger_TOKENS));
digits=[0-9]+;
ident=[A-Za-z][A-Za-z0-9_]*;
spaces=[\ \t];
newline=[\n\r]+;

%s COMMENT STRING;

%%
<INITIAL>type     => (Tokens.TYPE(yypos, yypos+4));
<INITIAL>var  	 => (Tokens.VAR(yypos, yypos+3));
<INITIAL>function => (Tokens.FUNCTION(yypos, yypos+8));
<INITIAL>break    => (Tokens.BREAK(yypos, yypos+5));
<INITIAL>of       => (Tokens.OF(yypos, yypos+2));
<INITIAL>end      => (Tokens.END(yypos, yypos+3));
<INITIAL>in       => (Tokens.IN(yypos, yypos+2));
<INITIAL>nil      => (Tokens.NIL(yypos, yypos+3));
<INITIAL>let      => (Tokens.LET(yypos, yypos+3));
<INITIAL>do	 => (Tokens.DO(yypos, yypos+2));
<INITIAL>to	 => (Tokens.TO(yypos, yypos+2));
<INITIAL>for	 => (Tokens.FOR(yypos, yypos+3));
<INITIAL>while	 => (Tokens.WHILE(yypos, yypos+5));
<INITIAL>else	 => (Tokens.ELSE(yypos, yypos+3));
<INITIAL>then     => (Tokens.THEN(yypos, yypos+4));
<INITIAL>if       => (Tokens.IF(yypos, yypos+2));
<INITIAL>array    => (Tokens.ARRAY(yypos, yypos+5));

<INITIAL>":="     => (Tokens.ASSIGN(yypos, yypos+2));
<INITIAL>"|"	 => (Tokens.OR(yypos, yypos+1));
<INITIAL>"&"	 => (Tokens.AND(yypos, yypos+1));
<INITIAL>">="	 => (Tokens.GE(yypos, yypos+2));
<INITIAL>">"	 => (Tokens.GT(yypos, yypos+2));
<INITIAL>"<="	 => (Tokens.LE(yypos, yypos+2));
<INITIAL>"<"	 => (Tokens.LT(yypos, yypos+2));
<INITIAL>"<>"	 => (Tokens.NEQ(yypos, yypos+2));
<INITIAL>"="	 => (Tokens.EQ(yypos, yypos+1));
<INITIAL>"/"	 => (Tokens.DIVIDE(yypos, yypos+1));
<INITIAL>"*"	 => (Tokens.TIMES(yypos, yypos+1));
<INITIAL>"-"	 => (Tokens.MINUS(yypos, yypos+1));
<INITIAL>"+"	 => (Tokens.PLUS(yypos, yypos+1));
<INITIAL>"."	 => (Tokens.DOT(yypos, yypos+1));
<INITIAL>"{"	 => (Tokens.LBRACE(yypos, yypos+1));
<INITIAL>"}"	 => (Tokens.RBRACE(yypos, yypos+1));
<INITIAL>"["	 => (Tokens.LBRACK(yypos, yypos+1));
<INITIAL>"]"	 => (Tokens.RBRACK(yypos, yypos+1));
<INITIAL>"("	 => (Tokens.LPAREN(yypos, yypos+1));
<INITIAL>")"	 => (Tokens.RPAREN(yypos, yypos+1));
<INITIAL>";"	 => (Tokens.SEMICOLON(yypos, yypos+1));
<INITIAL>":"	 => (Tokens.COLON(yypos, yypos+1));
<INITIAL>","      => (Tokens.COMMA(yypos, yypos+1));


<INITIAL>{digits}   => (Tokens.INT(valOf(Int.fromString yytext),
				 yypos,yypos+size yytext));
<INITIAL>{ident}    => (Tokens.ID(yytext,yypos,yypos+size yytext));

<INITIAL,COMMENT>"/*" => (YYBEGIN COMMENT;
			  commentLv := !commentLv + 1;
			  continue());
<COMMENT>"*/"         => (commentLv := !commentLv - 1;
			  if !commentLv = 0
			  then (YYBEGIN INITIAL; continue())
			  else continue());
<COMMENT>.            => (continue());

<INITIAL>"\"" => (YYBEGIN STRING;
		  strToken := "";
		  strPos   := 0;
		  continue());
<STRING>"\""  => (YYBEGIN INITIAL;
		  Tokens.STRING(!strToken, !strPos, yypos));
<STRING>.     => (strToken := !strToken ^ yytext; continue());

<INITIAL>{spaces}   => (continue());
<INITIAL>{newline}  => (lineNum := !lineNum+1;
		      linePos := yypos :: !linePos;
		      continue());
<INITIAL>.        => (ErrorMsg.error yypos ("illegal character " ^ yytext); continue());
