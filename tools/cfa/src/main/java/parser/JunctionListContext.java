package parser;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.NoSuchElementException;

/**
 * Handling vertically-aligned conjunction & disjunction lists (called
 * junction lists for short) is one of the most difficult parts of parsing
 * TLA+. This class keeps track of the current junction list parsing context
 * by storing a stack of the nested junction lists, their start columns, and
 * their types.
 * 
 * This implementation is adapted from the official TLA+ compiler (TLC) project
 * to work with ANTLR instead of JavaCC.
 */
public class JunctionListContext {

    /**
     * Enumeration of junction list types.
     */
    private enum JunctionListType {
        /**
         * Conjunction lists, which use the /\ bullet symbols.
         */
        CONJUNCTION,

        /**
         * Disjunction lists, which use the \/ bullet symbols.
         */
        DISJUNCTION
    }

    /**
     * A class holding information about a junction list.
     */
    private static class JunctionListInfo {
        /**
         * The type of the junction list, conjunction or disjunction.
         */
        public final JunctionListType type;

        /**
         * The column on which the junction list starts. This counts characters
         * from the beginning of the line, and is the number of characters before
         * the start of the bullet symbol. For example, if x denotes a space:
         * 
         * xxx/\
         * 
         * will have column value 3.
         */
        public final int column;

        /**
         * Constructs a new instance of the JunctionListInfo class.
         *
         * @param type The junction list type.
         * @param column The junction list alignment column.
         */
        public JunctionListInfo(JunctionListType type, int column) {
            this.type = type;
            this.column = column;
        }
    }

    /**
     * A stack tracking the nested junction list context.
     */
    private final Deque<JunctionListInfo> stack = new ArrayDeque<>();

    /**
     * Creates an empty JunctionListContext.
     */
    public JunctionListContext() {
    }

    /**
     * Determines whether the given token kind is a junction list bullet token.
     * In ANTLR context, we use token type constants.
     *
     * @param tokenType The token type from ANTLR lexer.
     * @return Whether the given token is a junction list bullet token.
     */
    private static boolean isJunctionListBulletToken(int tokenType) {
        // Use the generated ANTLR token constants
        return tokenType == 69 /* SLASH_BACKSLASH */ 
            || tokenType == 87 /* BACKSLASH_SLASH */;
    }

    /**
     * Resolves the given token type to either a conjunction or disjunction list type.
     *
     * @param tokenType The token type from ANTLR lexer.
     * @return Either a conjunction or disjunction list.
     * @throws IllegalArgumentException if invalid junction list token.
     */
    private static JunctionListType asJunctionListType(int tokenType) throws IllegalArgumentException {
        if (tokenType == 69 /* SLASH_BACKSLASH */) {
            return JunctionListType.CONJUNCTION;
        } else if (tokenType == 87 /* BACKSLASH_SLASH */) {
            return JunctionListType.DISJUNCTION;
        } else {
            throw new IllegalArgumentException("Invalid junction list token type: " + tokenType);
        }
    }

    /**
     * Pushes details of a new junction list onto the stack, indicating the
     * start of a new junction list.
     *
     * @param column The start column of the new junction list.
     * @param tokenType The token type from ANTLR lexer.
     * @throws IllegalArgumentException if invalid junction list token.
     */
    public void startNewJunctionList(int column, int tokenType) throws IllegalArgumentException {
        JunctionListType type = asJunctionListType(tokenType);
        System.out.println("DEBUG: Starting new junction list - column: " + column + ", type: " + type);
        this.stack.push(new JunctionListInfo(type, column));
    }

    /**
     * Removes the topmost junction list record, indicating the end of the
     * current junction list.
     *
     * @throws NoSuchElementException if not inside a junction list.
     */
    public void terminateCurrentJunctionList() throws NoSuchElementException {
        JunctionListInfo terminated = this.stack.pop();
        System.out.println("DEBUG: Terminating junction list - type: " + terminated.type + ", column: " + terminated.column);
    }

    /**
     * Returns true if the given token start column and type match the current
     * junction alignment and type, indicating it is another bullet in the
     * current junction list. If there are no currently active junction lists
     * then this is always false.
     *
     * @param column The token start column.
     * @param tokenType The token type from ANTLR lexer.
     * @return True if token is another bullet in the current junction list.
     */
    public boolean isNewBullet(int column, int tokenType) {
        JunctionListInfo headOrNull = this.stack.peekFirst();
        boolean result = headOrNull != null
            && isJunctionListBulletToken(tokenType)
            && headOrNull.column == column
            && headOrNull.type == asJunctionListType(tokenType);
        
        System.out.println("DEBUG: isNewBullet check - column: " + column + ", tokenType: " + tokenType + 
                          ", expected column: " + (headOrNull != null ? headOrNull.column : "null") + 
                          ", expected type: " + (headOrNull != null ? headOrNull.type : "null") + 
                          ", result: " + result);
        return result;
    }

    /**
     * Returns true if the given token start column is to the right of the
     * current junction list alignment, indicating it is probably contained
     * within the junction list. If there is no currently active junction list
     * then this is always true.
     *
     * @param column The start column of some token.
     * @return True if strictly greater than current junction list alignment.
     */
    public boolean isAboveCurrent(int column) {
        JunctionListInfo headOrNull = this.stack.peekFirst();
        return headOrNull == null || headOrNull.column < column;
    }

    /**
     * Returns true if we can start a new junction list at the given column
     * with the given token type. This is used to determine if we should
     * begin parsing a new junction list.
     *
     * @param column The start column of the token.
     * @param tokenType The token type from ANTLR lexer.
     * @return True if we can start a new junction list.
     */
    public boolean canStartNewJunctionList(int column, int tokenType) {
        boolean isBulletToken = isJunctionListBulletToken(tokenType);
        boolean isAbove = isAboveCurrent(column);
        boolean result = isBulletToken && isAbove;
        
        System.out.println("DEBUG: canStartNewJunctionList - column: " + column + ", tokenType: " + tokenType + 
                          ", isBulletToken: " + isBulletToken + ", isAbove: " + isAbove + 
                          ", currentStackSize: " + stack.size() + ", result: " + result);
        return result;
    }

    /**
     * Clears the junction list stack. This should be called when starting
     * to parse a new top-level construct.
     */
    public void clear() {
        this.stack.clear();
    }

    /**
     * Returns the current nesting depth of junction lists.
     *
     * @return The number of nested junction lists.
     */
    public int getDepth() {
        return this.stack.size();
    }
}