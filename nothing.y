%token ';' let static here mut goto type lambda to if '[' ']' int float char str var lopMAX_LEVEL lopASSIGN_LEVEL lopIN_LEVEL ropMAX_LEVEL ropIN_LEVEL ropASSIGN_LEVEL '=' ',' '{' '}' string '(' ')' matches for while in else cons
// this file only exists to check the grammar of the file


%define lr.type lalr

%%
Stmt : For
        | While
        | LexprASSIGN_LEVEL ';'
        | Let
		| goto var ';'
		| here var ';'
        | NonReturningIf;

Let : let LetList ';';

LetList : LetList ',' RexprASSIGN_LEVEL | RexprASSIGN_LEVEL;

VAR: var
    | mut var
    | static var
    | static mut var;

// Pattern : VAR
//        | '(' PatternList ')'
//        | '[' PatternList ']'
//        | cons '{' InnerStruct '}'
//;

// PatternList: PatternList ',' Pattern
//            | Pattern;

LexprMAX_LEVEL : LexprMAX_LEVEL lopMAX_LEVEL RexprMAX_LEVEL
            | RexprMAX_LEVEL;

RexprMAX_LEVEL : LexprASSIGN_LEVEL ropMAX_LEVEL RexprMAX_LEVEL
              | LexprASSIGN_LEVEL;

LexprASSIGN_LEVEL : LexprASSIGN_LEVEL lopASSIGN_LEVEL RexprASSIGN_LEVEL
                  | RexprASSIGN_LEVEL;

RexprASSIGN_LEVEL : LexprIN_LEVEL '=' RexprASSIGN_LEVEL
                  | LexprIN_LEVEL ropASSIGN_LEVEL RexprASSIGN_LEVEL
                  | LexprIN_LEVEL;

LexprIN_LEVEL : LexprIN_LEVEL lopIN_LEVEL RexprIN_LEVEL
            | RexprIN_LEVEL;

LexprIN_LEVELNoBrace : LexprIN_LEVELNoBrace lopIN_LEVEL RexprIN_LEVELNoBrace
            | RexprIN_LEVELNoBrace;
RexprIN_LEVEL : LexprIF_LEVEL ropIN_LEVEL RexprIN_LEVEL
              | LexprIF_LEVEL;
RexprIN_LEVELNoBrace : LexprIF_LEVELNoBrace ropIN_LEVEL RexprIN_LEVELNoBrace
              | LexprIF_LEVELNoBrace;

// PatternChain : PatternChain Pattern
//             | Pattern;

LexprIF_LEVEL : ReturningIf
               | lambda LexprAPPLICATION_LEVEL to LexprIF_LEVEL
			   | LexprAPPLICATION_LEVEL to LexprIF_LEVEL
               | LexprAPPLICATION_LEVEL
               ;

LexprIF_LEVELNoBrace : lambda LexprAPPLICATION_LEVELNoBrace to LexprIF_LEVELNoBrace
					 | LexprAPPLICATION_LEVELNoBrace to LexprIF_LEVELNoBrace
		             | LexprAPPLICATION_LEVELNoBrace
        	         ;

LexprAPPLICATION_LEVEL : LexprAPPLICATION_LEVEL Lit | Lit;

LexprAPPLICATION_LEVELNoBrace : LexprAPPLICATION_LEVELNoBrace LitNoBrace | LitNoBrace;

LitNoBrace : int
       | float
       | char
       | string
       | VAR
       | '(' lopASSIGN_LEVEL ')'
       | '(' lopIN_LEVEL ')'
       | '(' lopMAX_LEVEL ')'
       | '(' LexprIN_LEVEL lopIN_LEVEL ')'
       | '(' LexprMAX_LEVEL lopMAX_LEVEL ')'
       | '(' lopIN_LEVEL RexprIN_LEVEL ')'
       | '(' lopMAX_LEVEL RexprMAX_LEVEL ')'
       | '(' ropIN_LEVEL ')'
       | '(' ropMAX_LEVEL ')'
       | '(' ')'
       | '(' InnerList ')'
       | '(' InnerList '|' InnerList ')'
       | '[' InnerList ']';

Lit: LitNoBrace | '{' InnerMatch '}' | cons '{' InnerStruct '}' ;

InnerList : InnerList ',' LexprMAX_LEVEL
             | LexprMAX_LEVEL;

InnerMatch : InnerMatch ',' LexprAPPLICATION_LEVEL matches LexprIF_LEVEL
              | LexprAPPLICATION_LEVEL matches LexprIF_LEVEL;

InnerStruct : InnerStruct ',' var '=' RexprASSIGN_LEVEL
			 | InnerStruct ',' var
             | var '=' RexprASSIGN_LEVEL
			 | var;

ReturningIf : if RexprIN_LEVELNoBrace ReturningBlock else ReturningIf
               | ReturningBlock;

NonReturningIf : if RexprIN_LEVELNoBrace NonReturningBlock else NonReturningIf
			    | if RexprIN_LEVELNoBrace NonReturningBlock
                | NonReturningBlock;

For : for OldFor NonReturningBlock 
       | for InFor NonReturningBlock;

OldFor : '(' LexprASSIGN_LEVEL ';' LexprASSIGN_LEVEL ';' LexprASSIGN_LEVEL ')'
          | '(' LexprASSIGN_LEVEL ';' ';' LexprASSIGN_LEVEL ')'
          | '(' LexprASSIGN_LEVEL ';' LexprASSIGN_LEVEL ';' ')'
          | '(' LexprASSIGN_LEVEL ';' ';' ')'
          | '(' ';' LexprASSIGN_LEVEL ';' ')'
          | '(' ';' LexprASSIGN_LEVEL ';' LexprASSIGN_LEVEL ')'
          | '(' ';' ';' LexprASSIGN_LEVEL ')';

InFor : LexprIN_LEVEL in LexprIN_LEVELNoBrace;

ReturningBlock : '{' InnerBlock LexprASSIGN_LEVEL '}';

NonReturningBlock : '{' InnerBlock '}' | '{' '}';

InnerBlock : InnerBlock Stmt
              | Stmt;

While : while LexprIF_LEVELNoBrace NonReturningBlock;

%%

// [A {}]
