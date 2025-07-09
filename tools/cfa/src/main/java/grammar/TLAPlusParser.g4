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
module: AtLeast4Dash MODULE Identifier AtLeast4Dash LINE_BREAK
      (EXTENDS Identifier (COMMA Identifier)* LINE_BREAK)?
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
    | LINE_BREAK
    ;

variableDeclaration: (VARIABLE | VARIABLES) LINE_BREAK* INDENT? LINE_BREAK* Identifier (COMMA LINE_BREAK* INDENT? Identifier)* LINE_BREAK DEDENT?;

constantDeclaration: CONSTANTS LINE_BREAK* INDENT? LINE_BREAK* opDecl (COMMA LINE_BREAK* INDENT? opDecl)* LINE_BREAK* DEDENT?;

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
    INSTANCE Identifier LINE_BREAK?
    | INSTANCE Identifier WITH substitution (COMMA substitution)* LINE_BREAK?
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

moduleDefinition: nonFixLHS EQUALS instance LINE_BREAK?;

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
    | IF expression thenExpression elseExpression DEDENT? # IfExpression
    | CASE expression ARROW body (BRACKETS expression ARROW body)* (BRACKETS OTHER ARROW body)? # CaseExpression
    | LET (( INDENT? operatorDefinition | functionDefinition | moduleDefinition)LINE_BREAK? DEDENT?)+  INDENT?  BIGIN body DEDENT? # LetExpression
    | SLASH_BACKSLASH aobody # SlashBackslashExpression
    | BACKSLASH_SLASH aobody # BackslashSlashExpression
    | Number rightExpression  # NumberExpression
    | String rightExpression  # StringExpression
    | AT rightExpression  # AtExpression
    ;

thenExpression:
    THEN LINE_BREAK INDENT aobody
    | LINE_BREAK INDENT THEN LINE_BREAK? aobody ((INDENT aobody DEDENT)| aobody)*
    | THEN aobody
    ;

elseExpression:
    (LINE_BREAK? INDENT)? ELSE LINE_BREAK? aobody
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

// Enhanced body structure: supports both logical expressions and legacy aobody
body:
    LINE_BREAK? junctionItem
    ;

// Logical expression: logical terms connected by operators
logicalExpression:
    logicalTerm (logicalOperator logicalTerm)*
    ;

// Logical term: atomic statement or indented sub-expression
logicalTerm:
    atomicStatement                                    // Basic statement
    | LPAREN logicalExpression RPAREN                 // Parenthesized expression
    | LINE_BREAK INDENT logicalExpression DEDENT      // Indented sub-expression
    ;

// Logical operators: flexible forms of /\ and \/
logicalOperator:
    SLASH_BACKSLASH LINE_BREAK?                       // /\ with optional newline
    | BACKSLASH_SLASH LINE_BREAK?                     // \/ with optional newline  
    | LINE_BREAK SLASH_BACKSLASH                      // /\ after newline
    | LINE_BREAK BACKSLASH_SLASH                      // \/ after newline
    ;

// Atomic statement definition - basic unit in logical expressions  
atomicStatement:
    expression                   // General expression (includes all basic expressions)
    ;

// Structural statements (IF-THEN-ELSE, CASE, LET, etc.)
structuralStatement:
    ifStatement
    | caseStatement  
    | letStatement
    | quantifierStatement
    | chooseStatement
    ;

// IF-THEN-ELSE with proper indentation handling
ifStatement:
    IF predicateExpression thenClause elseClause?
    ;

thenClause:
    THEN LINE_BREAK? (INDENT logicalExpression DEDENT | logicalExpression)
    ;

elseClause:
    ELSE LINE_BREAK? (INDENT logicalExpression DEDENT | logicalExpression)
    ;

// CASE statement
caseStatement:
    CASE predicateExpression ARROW logicalExpression
    (LINE_BREAK? BRACKETS predicateExpression ARROW logicalExpression)*
    (LINE_BREAK? BRACKETS OTHER ARROW logicalExpression)?
    ;

// LET statement
letStatement:
    LET LINE_BREAK? INDENT?
    (operatorDefinition | functionDefinition | moduleDefinition) LINE_BREAK?
    (LINE_BREAK? (operatorDefinition | functionDefinition | moduleDefinition))*
    DEDENT? LINE_BREAK? BIGIN LINE_BREAK? (INDENT logicalExpression DEDENT | logicalExpression)
    ;

// Quantifier statements
quantifierStatement:
    (FORALL | EXISTS) quantifierBound (COMMA quantifierBound)* COLON logicalExpression
    | (FORALL | EXISTS | AA | EE) Identifier (COMMA Identifier)* COLON logicalExpression
    ;

// Choose statements
chooseStatement:
    CHOOSE identifierOrTuple COLON logicalExpression
    | CHOOSE identifierOrTuple IN predicateExpression COLON logicalExpression
    ;

// Assignment statements (primed and unprimed)
assignmentStatement:
    Identifier PRIME? EQUAL predicateExpression
    | Identifier LBRACKET predicateExpression RBRACKET PRIME? EQUAL predicateExpression
    | UNCHANGED DOUBLE_LESS (Identifier (COMMA Identifier)*)? DOUBLE_GREATER
    | UNCHANGED Identifier
    ;

// Predicate expressions (boolean-valued expressions)
predicateExpression:
    relationalExpression
    ;

// Relational expressions (comparisons)
relationalExpression:
    arithmeticExpression (relationalOperator arithmeticExpression)?
    ;

relationalOperator:
    EQUAL | SLASH_EQUAL | LESS | LESS_EQUAL | GREATER | GREATER_EQUAL
    | IN | NOTIN | SUBSET_s | SUBSETEQ
    ;

// Arithmetic expressions
arithmeticExpression:
    multiplicativeExpression ((PLUS | MINUS) multiplicativeExpression)*
    ;

multiplicativeExpression:
    powerExpression ((STAR | SLASH | DIV) powerExpression)*
    ;

powerExpression:
    unaryExpression (CARET unaryExpression)*
    ;

// Unary expressions
unaryExpression:
    (MINUS | TILDE | LNOT | NEG | DOMAIN | ENABLED | SUBSET | UNCHANGED | UNION)? primaryExpression
    ;

// Primary expressions
primaryExpression:
    atomicExpression postfixExpression*
    ;

// Postfix expressions (function calls, array access, etc.)
postfixExpression:
    LPAREN (argument (COMMA argument)*)? RPAREN  # PostfixFunctionCall
    | LBRACKET predicateExpression (COMMA predicateExpression)* RBRACKET  # ArrayAccess
    | DOT Identifier  # FieldAccess
    | PRIME  # PrimeExpression
    ;

// Atomic expressions (terminals and complex structures)
atomicExpression:
    generalIdentifier
    | Number
    | String  
    | setExpression
    | sequenceExpression
    | recordExpression
    | LPAREN predicateExpression RPAREN
    ;

// Set expressions
setExpression:
    LBRACE RBRACE  # EmptySetExpr
    | LBRACE predicateExpression (COMMA predicateExpression)* RBRACE  # EnumeratedSet
    | LBRACE identifierOrTuple IN predicateExpression COLON predicateExpression RBRACE  # SetComprehensionExpr
    | LBRACE predicateExpression COLON quantifierBound (COMMA quantifierBound)* RBRACE  # SetOfMaps
    ;

// Sequence expressions
sequenceExpression:
    DOUBLE_LESS DOUBLE_GREATER  # EmptySequenceExpr
    | DOUBLE_LESS predicateExpression (COMMA predicateExpression)* DOUBLE_GREATER  # EnumeratedSequence
    ;

// Record expressions
recordExpression:
    LBRACKET recordField (COMMA recordField)* RBRACKET
    | LBRACKET predicateExpression EXCEPT recordUpdate (COMMA recordUpdate)* RBRACKET
    ;

recordField:
    Identifier COLON predicateExpression
    | Identifier MAPSTO predicateExpression
    ;

recordUpdate:
    BANG recordSelector EQUAL predicateExpression
    ;

recordSelector:
    (DOT Identifier | LBRACKET predicateExpression RBRACKET)+
    ;

// Enhanced aobody with junction list support - fixes indentation-sensitive parsing
aobody:
    junctionList # junctionListAobody
    | statement # aobodyStatement
    ;

// Junction list: unified TLC-style implementation
junctionList:
    // Conjunction list: /\ items with TLC-style column alignment
    { getCurrentToken().getType() == 69 && junctionCtx.canStartNewJunctionList(getCurrentToken().getCharPositionInLine(), 69) }?
    slashBackslash=SLASH_BACKSLASH { junctionCtx.startNewJunctionList($slashBackslash.getCharPositionInLine(), 69); }
    junctionItem 
    (
        { junctionCtx.isNewBullet(getCurrentToken().getCharPositionInLine(), 69) }?
        nextSlashBackslash=SLASH_BACKSLASH 
        junctionItem
    )* 
    { junctionCtx.terminateCurrentJunctionList(); } # conjunctionList
    
    // Disjunction list: \/ items with TLC-style column alignment  
    | { getCurrentToken().getType() == 87 && junctionCtx.canStartNewJunctionList(getCurrentToken().getCharPositionInLine(), 87) }?
    backslashSlash=BACKSLASH_SLASH { junctionCtx.startNewJunctionList($backslashSlash.getCharPositionInLine(), 87); }
    junctionItem 
    (
        { junctionCtx.isNewBullet(getCurrentToken().getCharPositionInLine(), 87) }?
        nextBackslashSlash=BACKSLASH_SLASH 
        junctionItem
    )* 
    { junctionCtx.terminateCurrentJunctionList(); } # disjunctionList

    | statement # statementList
    ;

// Junction item: individual item in a junction list (TLC-style recursive)
junctionItem:
    // Try nested junction list first (both inline and indented)
    { getCurrentToken().getType() == 69 || getCurrentToken().getType() == 87 }?
    junctionList                                         // Recursive junction list
    | INDENT 
      { junctionCtx.clear(); }                           // Clear context for nested parsing
      junctionList 
      DEDENT                                             // Nested junction list with line breaks
    | statement                                          // Simple statement - fallback
    ;

// Enhanced statement with backward compatibility  
statement:
    expression+ LINE_BREAK?
    ;

// expression
//     : primaryExpression
//     | prefixExpression
//     | infixExpression
//     | postfixExpression
//     | specialExpression
//     ;


// primaryExpression
//     : generalIdentifier
//     | generalIdentifier LPAREN argument (COMMA argument)* RPAREN
//     | LPAREN expression RPAREN
//     | LBRACE RBRACE
//     | LBRACE expression (COMMA expression)* RBRACE
//     | Number
//     | String
//     | AT
//     ;


// prefixExpression
//     : generalPrefixOp expression
//     | FORALL quantifierBound (COMMA quantifierBound)* COLON expression
//     | EXISTS quantifierBound (COMMA quantifierBound)* COLON expression
//     | (FORALL | EXISTS | AA | EE) Identifier (COMMA Identifier)* COLON expression
//     | CHOOSE identifierOrTuple COLON expression
//     | CHOOSE identifierOrTuple IN expression COLON expression
//     | (WF_ | SF_) expression LPAREN expression RPAREN
//     ;


// infixExpression
//     : expression generalInfixOp expression
//     | expression (PAREN_BACKSLASH_X | TIMES) expression
//     ;


// postfixExpression
//     : expression generalPostfixOp
//     | expression LBRACKET expression (COMMA expression)* RBRACKET
//     | LBRACKET expression RBRACKET UNDERSCORE expression
//     | DOUBLE_LESS expression DOUBLE_GREATER UNDERSCORE expression
//     ;


// specialExpression
//     : LBRACE identifierOrTuple IN expression COLON expression RBRACE
//     | LBRACE expression COLON quantifierBound (COMMA quantifierBound)* RBRACE
//     | LBRACKET quantifierBound (COMMA quantifierBound)* MAPSTO expression RBRACKET
//     | LBRACKET expression ARROW expression RBRACKET
//     | LBRACKET (Identifier MAPSTO expression) (COMMA (Identifier MAPSTO expression))* RBRACKET
//     | LBRACKET (Identifier COLON expression) (COMMA (Identifier COLON expression))* RBRACKET
//     | LBRACKET expression EXCEPT (BANG (((DOT Identifier)| (LBRACKET expression (COMMA expression)* RBRACKET )))+ EQUAL expression) (COMMA (BANG (((DOT Identifier) | (LBRACKET expression (COMMA expression)* RBRACKET )))+ EQUAL expression))* RBRACKET
//     | DOUBLE_LESS expression (COMMA expression)* DOUBLE_GREATER
//     | IF expression THEN INDENT expression ELSE expression DEDENT
//     | CASE INDENT expression ARROW expression RBRACKET LBRACKET expression ARROW expression DEDENT
//     | CASE INDENT expression ARROW expression RBRACKET LBRACKET expression ARROW expression RBRACKET LBRACKET OTHER ARROW expression DEDENT
//     | LET (operatorDefinition | functionDefinition | moduleDefinition)+ BIGIN INDENT expression DEDENT
//     | INDENT SLASH_BACKSLASH expression+ DEDENT
//     | INDENT BACKSLASH_SLASH expression+ DEDENT
//     ;
