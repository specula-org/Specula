package parser;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.NoSuchElementException;
import org.antlr.v4.runtime.Token;

/**
 * Enhanced column-based junction list context that integrates with ANTLR parser.
 * This class follows TLC's approach to handle TLA+ junction lists by tracking
 * column positions instead of relying on INDENT/DEDENT tokens.
 */
public class ColumnBasedJunctionContext {

    /**
     * Enumeration of junction list types.
     */
    private enum JunctionListType {
        CONJUNCTION,    // /\ lists
        DISJUNCTION     // \/ lists
    }

    /**
     * Information about a junction list.
     */
    private static class JunctionListInfo {
        public final JunctionListType type;
        public final int column;
        public final int tokenType;

        public JunctionListInfo(JunctionListType type, int column, int tokenType) {
            this.type = type;
            this.column = column;
            this.tokenType = tokenType;
        }

        @Override
        public String toString() {
            return String.format("%s at column %d (token %d)", type, column, tokenType);
        }
    }

    /**
     * Stack tracking nested junction list context.
     */
    private final Deque<JunctionListInfo> stack = new ArrayDeque<>();

    /**
     * Token type constants for junction operators.
     * These should match your lexer's generated constants.
     */
    public static class TokenTypes {
        public static final int SLASH_BACKSLASH = 69;  // /\
        public static final int BACKSLASH_SLASH = 87;  // \/
        
        // You'll need to update these based on your actual generated token constants
        // Check SimpleTLAPlusLexer.tokens after generation
    }

    /**
     * Creates an empty junction context.
     */
    public ColumnBasedJunctionContext() {}

    /**
     * Determines if the given token type is a junction bullet.
     */
    private static boolean isJunctionListBulletToken(int tokenType) {
        return tokenType == TokenTypes.SLASH_BACKSLASH 
            || tokenType == TokenTypes.BACKSLASH_SLASH;
    }

    /**
     * Converts token type to junction list type.
     */
    private static JunctionListType asJunctionListType(int tokenType) {
        switch (tokenType) {
            case TokenTypes.SLASH_BACKSLASH:
                return JunctionListType.CONJUNCTION;
            case TokenTypes.BACKSLASH_SLASH:
                return JunctionListType.DISJUNCTION;
            default:
                throw new IllegalArgumentException("Invalid junction token: " + tokenType);
        }
    }

    /**
     * Starts a new junction list at the given column.
     * This should be called when the parser encounters the first /\ or \/ in a list.
     */
    public void startNewJunctionList(int column, int tokenType) {
        if (!isJunctionListBulletToken(tokenType)) {
            throw new IllegalArgumentException("Invalid junction token: " + tokenType);
        }
        
        JunctionListType type = asJunctionListType(tokenType);
        JunctionListInfo info = new JunctionListInfo(type, column, tokenType);
        stack.push(info);
        
        System.out.println("DEBUG: Started junction list - " + info);
    }

    /**
     * Terminates the current junction list.
     */
    public void terminateCurrentJunctionList() {
        if (stack.isEmpty()) {
            throw new NoSuchElementException("No active junction list to terminate");
        }
        
        JunctionListInfo terminated = stack.pop();
        System.out.println("DEBUG: Terminated junction list - " + terminated);
    }

    /**
     * Checks if the given token represents a new bullet in the current junction list.
     * This is used to determine if we should continue parsing the same junction list.
     */
    public boolean isNewBullet(int column, int tokenType) {
        if (stack.isEmpty()) {
            return false;
        }
        
        JunctionListInfo current = stack.peek();
        boolean result = isJunctionListBulletToken(tokenType)
            && current.column == column
            && current.type == asJunctionListType(tokenType);
        
        System.out.println("DEBUG: isNewBullet - column:" + column + " tokenType:" + tokenType + 
                          " expected:" + current + " result:" + result);
        return result;
    }

    /**
     * Checks if the given column is to the right of the current junction alignment.
     * This indicates the token is contained within the junction list.
     */
    public boolean isAboveCurrent(int column) {
        if (stack.isEmpty()) {
            return true;  // No active junction list, all columns are valid
        }
        
        JunctionListInfo current = stack.peek();
        return current.column < column;
    }

    /**
     * Checks if we can start a new junction list at the given position.
     */
    public boolean canStartNewJunctionList(int column, int tokenType) {
        boolean isBullet = isJunctionListBulletToken(tokenType);
        boolean isValidPosition = isAboveCurrent(column);
        
        return isBullet && isValidPosition;
    }

    /**
     * Utility method to check junction conditions using ANTLR tokens.
     */
    public boolean isNewBullet(Token token) {
        return isNewBullet(token.getCharPositionInLine(), token.getType());
    }

    /**
     * Utility method to check if token is above current junction using ANTLR tokens.
     */
    public boolean isAboveCurrent(Token token) {
        return isAboveCurrent(token.getCharPositionInLine());
    }

    /**
     * Utility method to start junction list using ANTLR tokens.
     */
    public void startNewJunctionList(Token token) {
        startNewJunctionList(token.getCharPositionInLine(), token.getType());
    }

    /**
     * Clears all junction list state. Useful when starting a new module or action.
     */
    public void clear() {
        stack.clear();
        System.out.println("DEBUG: Cleared junction context");
    }

    /**
     * Returns the current nesting depth.
     */
    public int getDepth() {
        return stack.size();
    }

    /**
     * Returns information about the current junction list, if any.
     */
    public String getCurrentInfo() {
        if (stack.isEmpty()) {
            return "No active junction list";
        }
        return "Current: " + stack.peek();
    }
}