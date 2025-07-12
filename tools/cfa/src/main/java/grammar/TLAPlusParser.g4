parser grammar TLAPlusParser;
@header {
package parser;
}
options { tokenVocab=TLAPlusLexer; }

@parser::members {
    // Junction list context for handling indentation-sensitive /\ and \/ parsing
    private parser.JunctionListContext junctionCtx = new parser.JunctionListContext();
}

// Analysis entry
module: AtLeast4Dash MODULE Identifier AtLeast4Dash
      (EXTENDS Identifier (COMMA Identifier)*)?
      (unit)*
      AtLeast4Equal
      ;

unit: 
      variableDeclaration
    | constantDeclaration
    | operatorDefinition
    | LOCAL operatorDefinition
    | functionDefinition
    | LOCAL functionDefinition
    | instance
    | LOCAL instance
    | moduleDefinition
    | LOCAL moduleDefinition
    | assumption
    | theorem
    | module
    | AtLeast4Dash
    ;

variableDeclaration: (VARIABLE | VARIABLES) Identifier (COMMA Identifier)*;

constantDeclaration: CONSTANTS opDecl (COMMA opDecl)*;

opDecl: 
    Identifier
    | Identifier LPAREN UNDERSCORE (COMMA UNDERSCORE)* RPAREN
    | prefixOp UNDERSCORE
    | UNDERSCORE infixOp UNDERSCORE
    | UNDERSCORE postfixOp
    ;

operatorDefinition: 
    nonFixLHS EQUALS  body
    | prefixOp Identifier EQUALS body
    | Identifier infixOp Identifier EQUALS body
    | Identifier postfixOp EQUALS body
    ;

nonFixLHS: 
    Identifier  
    | Identifier LPAREN (Identifier | opDecl) (COMMA (Identifier | opDecl))* RPAREN
    ;

functionDefinition: 
    Identifier LBRACKET (quantifierBound (COMMA quantifierBound)*) RBRACKET EQUALS body
    ;

quantifierBound: 
    (identifierOrTuple | (Identifier (COMMA Identifier)*)) IN expression
    ;

instance:
    INSTANCE Identifier
    | INSTANCE Identifier WITH substitution (COMMA substitution)*
    ;

substitution:
    Identifier ASSIGN argument
    | prefixOp ASSIGN argument
    | infixOp ASSIGN argument
    | postfixOp ASSIGN argument
    ;

argument:
    expression
    | generalPrefixOp
    | generalInfixOp
    | generalPostfixOp
    ;

instancePrefix: 
    (Identifier BANG)*
    | (Identifier LPAREN expression (COMMA expression)* RPAREN BANG)*
    ;

generalIdentifier: instancePrefix Identifier;
generalPrefixOp: instancePrefix prefixOp;
generalInfixOp: instancePrefix infixOp;
generalPostfixOp: instancePrefix postfixOp;

moduleDefinition: nonFixLHS EQUALS instance;

assumption: (ASSUME | ASSUMPTION | AXIOM) body;

theorem: THEOREM body;

rightExpression:
    generalPostfixOp rightExpression
    | LBRACKET expression (COMMA expression)* RBRACKET rightExpression
    | (PAREN_BACKSLASH_X | TIMES) expression rightExpression
    | generalInfixOp expression rightExpression
    | 
    ;
expression:                                                                                               
    generalIdentifier LPAREN argument (COMMA argument)* RPAREN rightExpression  # FunctionCall
    | generalPrefixOp expression rightExpression  # PrefixOperation
    | generalIdentifier rightExpression # IdentifierExpression
    | LPAREN expression RPAREN rightExpression  # ParenthesizedExpression
    | (FORALL | EXISTS) quantifierBound (COMMA quantifierBound)* COLON body # QuantifierExpression
    | (FORALL | EXISTS | AA | EE) Identifier (COMMA Identifier)* COLON body # SimpleQuantifierExpression
    | CHOOSE identifierOrTuple COLON body # ChooseExpression
    | CHOOSE identifierOrTuple IN expression COLON body # ChooseInExpression
    | LBRACE RBRACE  # EmptySet
    | LBRACE expression (COMMA expression)* RBRACE  # SetEnumeration  
    | LBRACE identifierOrTuple IN expression COLON body RBRACE  # SetComprehension
    | LBRACE expression COLON quantifierBound (COMMA quantifierBound)* RBRACE  # SetQuantifier
    | LBRACKET quantifierBound (COMMA quantifierBound)* MAPSTO expression RBRACKET # MappingExpression
    | LBRACKET expression ARROW expression RBRACKET # ArrowExpression
    | LBRACKET (Identifier MAPSTO expression) (COMMA (Identifier MAPSTO expression))* RBRACKET  # MapstoExpression
    | LBRACKET (Identifier COLON expression) (COMMA (Identifier COLON expression))* RBRACKET  # ColonExpression
    | LBRACKET expression EXCEPT (BANG (((DOT Identifier) | (LBRACKET expression (COMMA expression)* RBRACKET )))+ EQUAL expression) (COMMA (BANG (((DOT Identifier) | (LBRACKET expression (COMMA expression)* RBRACKET )))+ EQUAL expression))* RBRACKET  # ExceptExpression
    | DOUBLE_LESS (expression (COMMA expression)*)? DOUBLE_GREATER  # DoubleLessExpression
    | LBRACKET expression RBRACKET UNDERSCORE expression rightExpression  # BracketUnderscoreExpression
    | DOUBLE_LESS expression DOUBLE_GREATER UNDERSCORE expression  # DoubleLessUnderscoreExpression
    | (WF_ | SF_) expression LPAREN expression RPAREN rightExpression  # FairnessExpression
    | IF expression thenExpression elseExpression # IfExpression
    | CASE expression ARROW body (BRACKETS expression ARROW body)* (BRACKETS OTHER ARROW body)? # CaseExpression
    | LET (operatorDefinition | functionDefinition | moduleDefinition)+ BIGIN body # LetExpression
    | Number rightExpression  # NumberExpression
    | String rightExpression  # StringExpression
    | AT rightExpression  # AtExpression
    ;

thenExpression:
    THEN body                       
    ;

elseExpression:
    ELSE body                         
    ;

identifierOrTuple: Identifier | DOUBLE_LESS Identifier (COMMA Identifier)* DOUBLE_GREATER ;


reservedWord: 
    ASSUME | ASSUMPTION | AXIOM | CASE | CHOOSE | CONSTANT | CONSTANTS | DOMAIN |
    ELSE | ENABLED | EXCEPT | EXTENDS | IF | BIGIN | INSTANCE | LET |
    LOCAL | MODULE | OTHER | SF_ | SUBSET | THEN | THEOREM | UNCHANGED |
    UNION | VARIABLE | VARIABLES | WF_ | WITH
    ;


prefixOp: 
    MINUS | TILDE | LNOT | NEG | BRACKETS | ANGLE_BRACKETS | DOMAIN | ENABLED | SUBSET | UNCHANGED | UNION
    ;


infixOp: 
    CARET_CARET | BANG_BANG | HASH | HASH_HASH | DOLLAR | DOLLAR_DOLLAR | PERCENT | PERCENT_PERCENT | AMPERSAND | AMPERSAND_AMPERSAND |
    PAREN_PLUS | PAREN_MINUS | PAREN_DOT | PAREN_SLASH | PAREN_BACKSLASH_X | STAR | STAR_STAR | PLUS | PLUS_PLUS | MINUS | MINUS_PLUS_ARROW |
    MINUS_MINUS | MINUS_BAR | DOT_DOT | DOT_DOT_DOT | SLASH | SLASH_SLASH | SLASH_EQUAL | SLASH_BACKSLASH | COLON_COLON_EQUAL | COLON_EQUAL |
    COLON_GREATER | LESS | LESS_COLON | LESS_EQUAL_GREATER | EQUAL | EQUAL_GREATER | EQUAL_LESS | EQUAL_BAR | GREATER | GREATER_EQUAL | LESS_EQUAL|
    QUESTION | QUESTION_QUESTION | AT_AT | BACKSLASH | BACKSLASH_SLASH | CARET | BAR | BAR_MINUS | BAR_EQUAL | BAR_BAR | TILDE_GREATER |
    DOT | APPROX | ASYMP | BIGCIRC | BULLET | CAP | CDOT | CIRC | CONG | CUP | DIV | DOTEQ | EQUIV | GEQ | GG | IN | INTERSECT | LAND | LEQ |
    LL | LOR | O | ODOT | OMINUS | OPLUS | OSLASH | OTIMES | PREC | PRECEQ | PROPTO | SIM | SIMEQ | SQCAP | SQCUP | SQSQUBSET | SQSQUBSETEQ |
    SQSQUPSET | SQSQUPSETEQ | STAR_s | SUBSET_s | SUBSETEQ | SUCC | SUCCEQ | SUPSET_s | SUPSETEQ | UNION_s | UPLUS | WR | NOTIN
    ;

postfixOp: 
    CARET_PLUS | CARET_STAR | CARET_HASH | PRIME
    ;

body:
    junctionList
    ;


junctionList:
    // Disjunction list: \/ items
    (
        BACKSLASH_SLASH 
        junctionList
    )+ # disjunctionList
    
    // Conjunction list: /\ items
    | 
    (
        SLASH_BACKSLASH 
        junctionList
    )+ # conjunctionList
    
    | statement # statementList
    ;


statement:
    expression
    ;

