lexer grammar TLAPlusLexer;

options {
    superClass = TLAPlusLexerBase;
}

@lexer::header{
package parser;
}

tokens {
}

AtLeast4Dash: '----' ('-')*;
AtLeast4Equal: '====' ('=')*;

COMMA: ',';
ASSUME: 'ASSUME';
ASSUMPTION: 'ASSUMPTION';
AXIOM: 'AXIOM';
CASE: 'CASE';
CHOOSE: 'CHOOSE';
CONSTANT: 'CONSTANT';
CONSTANTS: 'CONSTANTS';
DOMAIN: 'DOMAIN';
ELSE: 'ELSE';
ENABLED: 'ENABLED';
EXCEPT: 'EXCEPT';
EXTENDS: 'EXTENDS';
IF: 'IF';
BIGIN: 'IN';
INSTANCE: 'INSTANCE';
LET: 'LET';
LOCAL: 'LOCAL';
MODULE: 'MODULE';
OTHER: 'OTHER';
SF_: 'SF_';
SUBSET: 'SUBSET';
THEN: 'THEN';
THEOREM: 'THEOREM';
UNCHANGED: 'UNCHANGED';
UNION: 'UNION';
VARIABLE: 'VARIABLE';
VARIABLES: 'VARIABLES';
WF_: 'WF_';
WITH: 'WITH';

MINUS: '-';
TILDE: '~';
LNOT: '\\lnot';
NEG: '\\neg';
BRACKETS: '[]';
ANGLE_BRACKETS: '<>';

CARET_CARET: '^^';
BANG_BANG: '!!';
HASH: '#';
HASH_HASH: '##';
DOLLAR: '$';
DOLLAR_DOLLAR: '$$';
PERCENT: '%';
PERCENT_PERCENT: '%%';
AMPERSAND: '&';
AMPERSAND_AMPERSAND: '&&';
PAREN_PLUS: '(+)';
PAREN_MINUS: '(-)';
PAREN_DOT: '(.)';
PAREN_SLASH: '(/)';
PAREN_BACKSLASH_X: '(\\X)';
STAR: '*';
STAR_STAR: '**';
PLUS: '+';
PLUS_PLUS: '++';
MINUS_PLUS_ARROW: '-+->';
MINUS_MINUS: '--';
MINUS_BAR: '-|';
DOT_DOT: '..';
DOT_DOT_DOT: '...';
SLASH: '/';
SLASH_SLASH: '//';
SLASH_EQUAL: '/=';
SLASH_BACKSLASH: '/\\';
COLON_COLON_EQUAL: '::=';
COLON_EQUAL: ':=';
COLON_GREATER: ':>';
LESS: '<';
LESS_COLON: '<:';
LESS_EQUAL: '<=';
LESS_EQUAL_GREATER: '<=>';
EQUAL: '=';
EQUAL_GREATER: '=>';
EQUAL_LESS: '=<';
EQUAL_BAR: '=|';
GREATER: '>';
GREATER_EQUAL: '>=';
QUESTION: '?';
QUESTION_QUESTION: '??';
AT_AT: '@@';
BACKSLASH: '\\';
BACKSLASH_SLASH: '\\/';
CARET: '^';
BAR: '|';
BAR_MINUS: '|-';
BAR_EQUAL: '|=';
BAR_BAR: '||';
TILDE_GREATER: '~>';
DOT: '.';
APPROX: '\\approx';
ASYMP: '\\asymp';
BIGCIRC: '\\bigcirc';
BULLET: '\\bullet';
CAP: '\\cap';
CDOT: '\\cdot';
CIRC: '\\circ';
CONG: '\\cong';
CUP: '\\cup';
DIV: '\\div';
DOTEQ: '\\doteq';
EQUIV: '\\equiv';
GEQ: '\\geq';
GG: '\\gg';
IN: '\\in';
NOTIN: '\\notin';
INTERSECT: '\\intersect';
LAND: '\\land';
LEQ: '\\leq';
LL: '\\ll';
LOR: '\\lor';
O: '\\o';
ODOT: '\\odot';
OMINUS: '\\ominus';
OPLUS: '\\oplus';
OSLASH: '\\oslash';
OTIMES: '\\otimes';
PREC: '\\prec';
PRECEQ: '\\preceq';
PROPTO: '\\propto';
SIM: '\\sim';
SIMEQ: '\\simeq';
SQCAP: '\\sqcap';
SQCUP: '\\sqcup';
SQSQUBSET: '\\sqsubset';
SQSQUBSETEQ: '\\sqsubseteq';
SQSQUPSET: '\\sqsupset';
SQSQUPSETEQ: '\\sqsupseteq';
STAR_s: '\\star';
SUBSET_s: '\\subset';
SUBSETEQ: '\\subseteq';
SUCC: '\\succ';
SUCCEQ: '\\succeq';
SUPSET_s: '\\supset';
SUPSETEQ: '\\supseteq';
UNION_s: '\\union';
UPLUS: '\\uplus';
WR: '\\wr';

CARET_PLUS: '^+';
CARET_STAR: '^*';
CARET_HASH: '^#';
PRIME: '\'';


LPAREN: '(' {this.incParenLevel();};
RPAREN: ')' {this.decParenLevel();};
EQUALS: '==';
UNDERSCORE: '_';
ASSIGN: '<-';
BANG: '!';
LBRACKET: '[' {this.incBracketLevel();};
RBRACKET: ']' {this.decBracketLevel();};
LBRACE: '{' {this.incBraceLevel();};
RBRACE: '}' {this.decBraceLevel();};
DOUBLE_LESS: '<<' {this.incAngleLevel();};
DOUBLE_GREATER: '>>' {this.decAngleLevel();};
AT: '@';
COLON: ':';
TIMES: '\\times';


FORALL: '\\A';
EXISTS: '\\E';
AA: '\\AA';
EE: '\\EE';


MAPSTO: '|->';
ARROW: '->';



Identifier: (NameChar* Letter NameChar*)
    { !getText().startsWith("WF_") && !getText().startsWith("SF_") }?
    ;

Number: 
     Numeral+ 
    | Numeral* '.' Numeral+
    | '\\b' [0-1]+
    | '\\B' [0-1]+
    | '\\o' [0-7]+
    | '\\O' [0-7]+
    | '\\h' [0-9a-fA-F]+
    | '\\H' [0-9a-fA-F]+
    ;

String: '"' (~["])* '"' ;

fragment NameChar: Letter | Numeral | UNDERSCORE ;
fragment Letter: [a-zA-Z];
fragment Numeral: [0-9];





//NameChar: Letter | Numeral | UNDERSCORE ;
//
//Name: (NameChar* Letter NameChar*)
//    { !getText().startsWith("WF_") && !getText().startsWith("SF_") }?
//    ;
//Identifier: Name
//    { !getText().matches("ASSUME|ASSUMPTION|AXIOM|CASE|CHOOSE|CONSTANT|CONSTANTS|DOMAIN|ELSE|ENABLED|EXCEPT|EXTENDS|IF|BIGIN|INSTANCE|LET|LOCAL|MODULE|OTHER|SF_|SUBSET|THEN|THEOREM|UNCHANGED|UNION|VARIABLE|VARIABLES|WF_|WITH") }?
//    ;

// IdentifierOrTuple: Identifier | DOUBLE_LESS Identifier (COMMA Identifier)* DOUBLE_GREATER ;


NEWLINE   : RN             {this.HandleNewLine();} -> channel(HIDDEN);
WS        : [ \t]+         {this.HandleSpaces();} -> channel(HIDDEN);
COMMENT   : '\\*' ~[\r\n\f]* -> channel(HIDDEN);
fragment RN: '\r'? '\n';

//BLANKS: (SPACES|COMMENT)+ -> skip;
//
//fragment SPACES: [ \t]+;
//
//fragment COMMENT: '\\*' ~[\r\n\f]*;