package parser;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.List;

import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CommonToken;
import org.antlr.v4.runtime.Lexer;
import org.antlr.v4.runtime.Token;

public abstract class TLAPlusLexerBase extends Lexer {
    public static int TabSize = 8;

    // Enhanced bracket tracking for different bracket types
    private int _parenthesesLevel = 0;    // ()
    private int _bracketLevel = 0;        // []
    private int _braceLevel = 0;          // {}
    private int _angleLevel = 0;          // <<>>

    // The stack that keeps track of the indentation level
    private final Deque<Integer> _indents = new ArrayDeque<>();
    
    // Context-aware indentation stack
    private final Deque<IndentContext> _indentContexts = new ArrayDeque<>();
    
    // Advanced conjunction/disjunction tracking
    private final Deque<LogicalOperatorContext> _logicalOpStack = new ArrayDeque<>();
    private final List<LogicalOperatorContext> _logicalOpHistory = new ArrayList<>();
    
    // Token analysis buffer for context determination
    private final Deque<Token> _recentTokens = new ArrayDeque<>();
    private static final int MAX_RECENT_TOKENS = 10;

    // A circular buffer where extra tokens are pushed on (see the NEWLINE and WS lexer rules)
    private int _firstTokensInd;
    private int _lastTokenInd;
    private Token[] _buffer = new Token[32];
    private Token _lastToken;
    
    // Inner class for indentation context tracking
    private static class IndentContext {
        int indentLevel;
        ContextType type;
        int lineNumber;
        LogicalOperatorContext associatedLogicalOp;
        
        IndentContext(int level, ContextType contextType, int line) {
            this.indentLevel = level;
            this.type = contextType;
            this.lineNumber = line;
            this.associatedLogicalOp = null;
        }
        
        IndentContext(int level, ContextType contextType, int line, LogicalOperatorContext logicalOp) {
            this.indentLevel = level;
            this.type = contextType;
            this.lineNumber = line;
            this.associatedLogicalOp = logicalOp;
        }
        
        enum ContextType {
            GENERAL,           // General indentation
            CONJUNCTION,       // /\ context
            DISJUNCTION,       // \/ context
            STRUCTURAL         // if/then/else structures
        }
    }
    
    // Class for tracking logical operators (/\ and \/)
    private static class LogicalOperatorContext {
        OperatorType type;
        int indentLevel;
        int lineNumber;
        int charPosition;
        boolean isNested;
        LogicalOperatorContext parent;
        
        LogicalOperatorContext(OperatorType opType, int indent, int line, int charPos) {
            this.type = opType;
            this.indentLevel = indent;
            this.lineNumber = line;
            this.charPosition = charPos;
            this.isNested = false;
            this.parent = null;
        }
        
        enum OperatorType {
            CONJUNCTION,    // /\
            DISJUNCTION     // \/
        }
        
        @Override
        public String toString() {
            return String.format("%s at line %d, indent %d, char %d", 
                type, lineNumber, indentLevel, charPosition);
        }
    }

    protected TLAPlusLexerBase(CharStream input) {
        super(input);
    }

    @Override
    public void emit(Token token) {
        super.setToken(token);

        if (_buffer[_firstTokensInd] != null)
        {
            _lastTokenInd = IncTokenInd(_lastTokenInd);

            if (_lastTokenInd == _firstTokensInd)
            {
                // Enlarge buffer
                Token[] newArray = new Token[_buffer.length * 2];
                int destInd = newArray.length - (_buffer.length - _firstTokensInd);

                System.arraycopy(_buffer, 0, newArray, 0, _firstTokensInd);
                System.arraycopy(_buffer, _firstTokensInd, newArray, destInd, _buffer.length - _firstTokensInd);

                _firstTokensInd = destInd;
                _buffer = newArray;
            }
        }

        _buffer[_lastTokenInd] = token;
        _lastToken = token;
        
        // Track recent tokens for context analysis
        trackRecentToken(token);
        
        // Detect logical operators (/\ and \/)
        detectLogicalOperator(token);
    }

    @Override
    public Token nextToken() {
        // Check if the end-of-file is ahead and there are still some DEDENTS expected.
        // Simplified: no INDENT/DEDENT processing
        // if (_input.LA(1) == EOF && _indents.size() > 0) {
        //     // Previous INDENT/DEDENT logic removed
        // }

        Token next = super.nextToken();

        if (_buffer[_firstTokensInd] == null)
        {
            return next;
        }

        Token result = _buffer[_firstTokensInd];
        _buffer[_firstTokensInd] = null;

        if (_firstTokensInd != _lastTokenInd)
        {
            _firstTokensInd = IncTokenInd(_firstTokensInd);
        }

        return result;
    }

    protected void HandleNewLine() {
        emit(TLAPlusLexer.NEWLINE, HIDDEN, getText());

        char next = (char) _input.LA(1);

        // Process whitespaces in HandleSpaces
        if (next != ' ' && next != '\t' && IsNotNewLineOrComment(next))
        {
            ProcessNewLine(0);
        }
    }

    protected void HandleSpaces() {
        char next = (char) _input.LA(1);

        if ((_lastToken == null || _lastToken.getType() == TLAPlusLexer.NEWLINE) && IsNotNewLineOrComment(next))
        {
            // Calculates the indentation of the provided spaces, taking the
            // following rules into account:
            //
            // "Tabs are replaced (from left to right) by one to eight spaces
            //  such that the total number of characters up to and including
            //  the replacement is a multiple of eight [...]"
            //
            //  -- https://docs.TLAPlus.org/3.1/reference/lexical_analysis.html#indentation

            int indent = 0;
            String text = getText();

            for (int i = 0; i < text.length(); i++) {
                indent += text.charAt(i) == '\t' ? TabSize - indent % TabSize : 1;
            }

            ProcessNewLine(indent);
        }

        emit(TLAPlusLexer.WS, HIDDEN, getText());
    }

    // Legacy methods - replaced by specific bracket tracking
    protected void IncIndentLevel() {
        // Deprecated - use specific bracket level methods
    }

    protected void DecIndentLevel() {
        // Deprecated - use specific bracket level methods
    }

    // Check if we are inside any type of brackets
    private boolean isInsideBrackets() {
        return _parenthesesLevel > 0 || _bracketLevel > 0 || 
               _braceLevel > 0 || _angleLevel > 0;
    }
    
    private boolean IsNotNewLineOrComment(char next) {
        return !isInsideBrackets() && next != '\r' && next != '\n' && next != '\f' && next != '#';
    }

    private void ProcessNewLine(int indent) {
        // Simplified: no LINE_BREAK token
        // emit(TLAPlusLexer.LINE_BREAK);
        
        // Skip indentation processing if we are inside brackets
        if (isInsideBrackets()) {
            return;
        }

        int previous = _indents.size() == 0 ? 0 : _indents.peek();
        
        // Debug: print indentation info
        System.out.println("DEBUG ProcessNewLine: line=" + getLine() + ", indent=" + indent + ", previous=" + previous + ", stack=" + _indents);

        if (indent > previous) {
            _indents.push(indent);
            // Determine context for this indentation level
            IndentContext context = determineContext(indent);
            _indentContexts.push(context);
            System.out.println("DEBUG: Emitting INDENT, new stack=" + _indents);
            // Simplified: no INDENT token
            // emit(TLAPlusLexer.INDENT);
        } else if (indent < previous) {
            // Standard DEDENT processing - generate DEDENT tokens until we reach the target indent
            System.out.println("DEBUG: Standard DEDENT processing from " + previous + " to " + indent);
            while (_indents.size() != 0 && _indents.peek() > indent) {
                System.out.println("DEBUG: Emitting DEDENT, popping " + _indents.peek());
                // Simplified: no DEDENT token
                // emit(TLAPlusLexer.DEDENT);
                _indents.pop();
                
                // Also clean up context stacks
                if (!_indentContexts.isEmpty()) {
                    _indentContexts.pop();
                }
            }
            System.out.println("DEBUG: Standard DEDENT finished: final stack=" + _indents);
        }
    }
    
    // Smart dedent matching that considers logical operator contexts
    private void smartDedentMatching(int targetIndent) {
        // Find the correct indentation level to match
        int targetLevel = findMatchingIndentLevel(targetIndent);
        
        System.out.println("DEBUG smartDedentMatching: targetIndent=" + targetIndent + ", targetLevel=" + targetLevel + ", current stack=" + _indents);
        
        // Emit DEDENT tokens until we reach the target level
        while (_indents.size() != 0 && _indents.peek() > targetLevel) {
            System.out.println("DEBUG: Emitting DEDENT, popping " + _indents.peek());
            // Simplified: no DEDENT token
            // emit(TLAPlusLexer.DEDENT);
            int poppedIndent = _indents.pop();
            
            // Remove corresponding context and clean up logical operator stack
            if (!_indentContexts.isEmpty()) {
                IndentContext poppedContext = _indentContexts.pop();
                cleanupLogicalOperatorStack(poppedIndent, poppedContext);
            }
        }
        
        System.out.println("DEBUG smartDedentMatching finished: final stack=" + _indents);
    }
    
    // Find the correct indentation level to match, considering logical operators
    private int findMatchingIndentLevel(int currentIndent) {
        // Strategy: Look for the nearest matching logical operator indentation
        // or fall back to standard indentation matching
        
        // First, try to find a matching logical operator context
        LogicalOperatorContext matchingOp = findMatchingLogicalOperator(currentIndent);
        if (matchingOp != null) {
            System.out.println("DEBUG: Found matching logical operator: " + matchingOp + ", returning indentLevel=" + matchingOp.indentLevel);
            return matchingOp.indentLevel;
        }
        
        // Fallback to standard indentation matching
        // Find the largest indentation level that is <= currentIndent
        int bestMatch = 0;
        for (Integer indentLevel : _indents) {
            if (indentLevel <= currentIndent && indentLevel > bestMatch) {
                bestMatch = indentLevel;
            }
        }
        
        System.out.println("DEBUG: No logical operator match, using standard matching: bestMatch=" + bestMatch);
        return bestMatch;
    }
    
    // Find a logical operator that should match the current indentation
    private LogicalOperatorContext findMatchingLogicalOperator(int currentIndent) {
        // Look through logical operator history in reverse order
        for (int i = _logicalOpHistory.size() - 1; i >= 0; i--) {
            LogicalOperatorContext op = _logicalOpHistory.get(i);
            
            // Check if this operator's indentation matches or is a valid parent
            if (op.indentLevel == currentIndent) {
                return op; // Exact match
            }
            
            // For nested structures, check if this could be a valid parent
            if (op.indentLevel < currentIndent && 
                (op.type == LogicalOperatorContext.OperatorType.CONJUNCTION || 
                 op.type == LogicalOperatorContext.OperatorType.DISJUNCTION)) {
                
                // Check if there's a valid continuation pattern
                if (isValidLogicalOperatorContinuation(op, currentIndent)) {
                    return op;
                }
            }
        }
        
        return null;
    }
    
    // Check if the current indentation represents a valid continuation of a logical operator
    private boolean isValidLogicalOperatorContinuation(LogicalOperatorContext op, int currentIndent) {
        // This is where we implement the TLA+ specific rules for /\ and \/ continuation
        // In TLA+, logical operators can have their continuations at various indentation levels
        
        // Rule 1: Exact alignment with the operator
        if (currentIndent == op.indentLevel) {
            return true;
        }
        
        // Rule 2: Indentation that aligns with previous elements in the same logical block
        // This requires analyzing the structure more deeply
        
        // For now, accept indentations that are reasonable continuations
        return currentIndent > op.indentLevel && (currentIndent - op.indentLevel) <= 8;
    }
    
    // Clean up logical operator stack when dedenting
    private void cleanupLogicalOperatorStack(int poppedIndent, IndentContext poppedContext) {
        // Remove logical operators that are no longer relevant
        while (!_logicalOpStack.isEmpty() && 
               _logicalOpStack.peekLast().indentLevel >= poppedIndent) {
            _logicalOpStack.removeLast();
        }
    }
    
    // Track recent tokens for context analysis
    private void trackRecentToken(Token token) {
        _recentTokens.addLast(token);
        if (_recentTokens.size() > MAX_RECENT_TOKENS) {
            _recentTokens.removeFirst();
        }
    }
    
    // Detect logical operators and track their context
    private void detectLogicalOperator(Token token) {
        if (token.getType() == TLAPlusLexer.SLASH_BACKSLASH) { // /\
            int currentIndent = getCurrentIndentLevel();
            LogicalOperatorContext conjCtx = new LogicalOperatorContext(
                LogicalOperatorContext.OperatorType.CONJUNCTION,
                currentIndent,
                token.getLine(),
                token.getCharPositionInLine()
            );
            
            // Check if this is nested within another logical operator
            if (!_logicalOpStack.isEmpty()) {
                conjCtx.parent = _logicalOpStack.peekLast();
                conjCtx.isNested = true;
            }
            
            _logicalOpStack.addLast(conjCtx);
            _logicalOpHistory.add(conjCtx);
            
        } else if (token.getType() == TLAPlusLexer.BACKSLASH_SLASH) { // \/
            int currentIndent = getCurrentIndentLevel();
            LogicalOperatorContext disjCtx = new LogicalOperatorContext(
                LogicalOperatorContext.OperatorType.DISJUNCTION,
                currentIndent,
                token.getLine(),
                token.getCharPositionInLine()
            );
            
            // Check if this is nested within another logical operator
            if (!_logicalOpStack.isEmpty()) {
                disjCtx.parent = _logicalOpStack.peekLast();
                disjCtx.isNested = true;
            }
            
            _logicalOpStack.addLast(disjCtx);
            _logicalOpHistory.add(disjCtx);
        }
    }
    
    // Get current indentation level based on the current line's indentation
    private int getCurrentIndentLevel() {
        // Return the line's indentation level, not the token's character position
        // This should be the number of spaces/tabs at the beginning of the line
        
        // Use the current stack state to determine the line's indentation
        // The stack always reflects the current indentation level
        return _indents.size() == 0 ? 0 : _indents.peek();
    }
    
    // Determine the context type for a new indentation level
    private IndentContext determineContext(int indent) {
        // Analyze recent tokens to determine context
        LogicalOperatorContext recentLogicalOp = findMostRecentLogicalOperator(indent);
        
        if (recentLogicalOp != null) {
            if (recentLogicalOp.type == LogicalOperatorContext.OperatorType.CONJUNCTION) {
                return new IndentContext(indent, IndentContext.ContextType.CONJUNCTION, getLine(), recentLogicalOp);
            } else if (recentLogicalOp.type == LogicalOperatorContext.OperatorType.DISJUNCTION) {
                return new IndentContext(indent, IndentContext.ContextType.DISJUNCTION, getLine(), recentLogicalOp);
            }
        }
        
        // Check for structural keywords (IF, THEN, ELSE, etc.)
        if (hasRecentStructuralKeyword()) {
            return new IndentContext(indent, IndentContext.ContextType.STRUCTURAL, getLine());
        }
        
        return new IndentContext(indent, IndentContext.ContextType.GENERAL, getLine());
    }
    
    // Find the most recent logical operator that could affect this indentation
    private LogicalOperatorContext findMostRecentLogicalOperator(int currentIndent) {
        // Look through recent logical operators to find one that matches
        for (int i = _logicalOpHistory.size() - 1; i >= 0; i--) {
            LogicalOperatorContext op = _logicalOpHistory.get(i);
            // If we find an operator at a similar or parent indentation level
            if (op.indentLevel <= currentIndent) {
                return op;
            }
        }
        return null;
    }
    
    // Check if recent tokens contain structural keywords
    private boolean hasRecentStructuralKeyword() {
        for (Token token : _recentTokens) {
            int tokenType = token.getType();
            if (tokenType == TLAPlusLexer.IF || tokenType == TLAPlusLexer.THEN || 
                tokenType == TLAPlusLexer.ELSE || tokenType == TLAPlusLexer.CASE ||
                tokenType == TLAPlusLexer.LET || tokenType == TLAPlusLexer.BIGIN) {
                return true;
            }
        }
        return false;
    }
    
    // Bracket level management methods
    public void incParenLevel() {
        _parenthesesLevel++;
    }
    
    public void decParenLevel() {
        if (_parenthesesLevel > 0) {
            _parenthesesLevel--;
        }
    }
    
    public void incBracketLevel() {
        _bracketLevel++;
    }
    
    public void decBracketLevel() {
        if (_bracketLevel > 0) {
            _bracketLevel--;
        }
    }
    
    public void incBraceLevel() {
        _braceLevel++;
    }
    
    public void decBraceLevel() {
        if (_braceLevel > 0) {
            _braceLevel--;
        }
    }
    
    public void incAngleLevel() {
        _angleLevel++;
    }
    
    public void decAngleLevel() {
        if (_angleLevel > 0) {
            _angleLevel--;
        }
    }

    private int IncTokenInd(int ind) {
        return (ind + 1) % _buffer.length;
    }

    private void emit(int tokenType) {
        emit(tokenType, DEFAULT_TOKEN_CHANNEL, "");
    }

    private void emit(int tokenType, int channel, String text) {
        int charIndex = getCharIndex();
        CommonToken token = new CommonToken(_tokenFactorySourcePair, tokenType, channel, charIndex - text.length(), charIndex - 1);
        token.setLine(getLine());
        token.setCharPositionInLine(getCharPositionInLine());
        token.setText(text);

        emit(token);
    }
}