package CFG;

import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.RuleNode;
import org.antlr.v4.runtime.tree.TerminalNode;
import parser.TLAPlusParser;
import parser.TLAPlusParserBaseVisitor;

/**
 * A visitor for printing AST structure in a readable format
 */
public class ASTDebugVisitor extends TLAPlusParserBaseVisitor<Void> {
    private int indentLevel = 0;
    private static final String INDENT = "  ";

    public void printAST(ParseTree tree) {
        System.out.println("=== AST Structure ===");
        visit(tree);
        System.out.println("=== End AST ===");
    }

    @Override
    public Void visit(ParseTree tree) {
        if (tree instanceof RuleNode) {
            RuleNode ruleNode = (RuleNode) tree;
            String ruleName = getRuleName(ruleNode);
            String nodeInfo = getNodeInfo(ruleNode);
            
            printIndented(ruleName + nodeInfo);
            
            indentLevel++;
            for (int i = 0; i < tree.getChildCount(); i++) {
                visit(tree.getChild(i));
            }
            indentLevel--;
        } else if (tree instanceof TerminalNode) {
            TerminalNode terminal = (TerminalNode) tree;
            String tokenText = terminal.getText();
            String tokenInfo = String.format("[%s]", 
                tokenText.length() > 20 ? tokenText.substring(0, 20) + "..." : tokenText);
            printIndented("TERMINAL: " + tokenInfo);
        }
        return null;
    }

    private String getRuleName(RuleNode node) {
        if (node instanceof TLAPlusParser.ModuleContext) return "MODULE";
        if (node instanceof TLAPlusParser.UnitContext) return "UNIT";
        if (node instanceof TLAPlusParser.OperatorDefinitionContext) return "OPERATOR_DEF";
        if (node instanceof TLAPlusParser.BodyContext) return "BODY";
        if (node instanceof TLAPlusParser.JunctionListContext) {
            if (node instanceof TLAPlusParser.JunctionItemsListContext) return "JUNCTION_ITEMS_LIST";
            if (node instanceof TLAPlusParser.StatementListContext) return "STATEMENT_LIST";
            return "JUNCTION_LIST";
        }
        if (node instanceof TLAPlusParser.JunctionItemsContext) {
            if (node instanceof TLAPlusParser.ConjunctionListContext) return "CONJUNCTION_LIST";
            if (node instanceof TLAPlusParser.DisjunctionListContext) return "DISJUNCTION_LIST";
            return "JUNCTION_ITEMS";
        }
        if (node instanceof TLAPlusParser.StatementContext) return "STATEMENT";
        if (node instanceof TLAPlusParser.ExpressionContext) return "EXPRESSION";
        if (node instanceof TLAPlusParser.VariableDeclarationContext) return "VARIABLE_DECLARATION";
        if (node instanceof TLAPlusParser.ConstantDeclarationContext) return "CONSTANT_DECLARATION";
        
        // Default fallback
        return node.getClass().getSimpleName().replace("Context", "").toUpperCase();
    }

    private String getNodeInfo(RuleNode node) {
        if (node instanceof TLAPlusParser.JunctionItemsContext) {
            TLAPlusParser.JunctionItemsContext jctx = (TLAPlusParser.JunctionItemsContext) node;
            if (jctx instanceof TLAPlusParser.ConjunctionListContext) {
                TLAPlusParser.ConjunctionListContext cctx = (TLAPlusParser.ConjunctionListContext) jctx;
                return String.format(" (items: %d)", cctx.statement().size());
            } else if (jctx instanceof TLAPlusParser.DisjunctionListContext) {
                TLAPlusParser.DisjunctionListContext dctx = (TLAPlusParser.DisjunctionListContext) jctx;
                return String.format(" (items: %d)", dctx.statement().size());
            }
        }
        
        if (node instanceof TLAPlusParser.OperatorDefinitionContext) {
            TLAPlusParser.OperatorDefinitionContext opCtx = (TLAPlusParser.OperatorDefinitionContext) node;
            if (opCtx.nonFixLHS() != null && opCtx.nonFixLHS().Identifier() != null && !opCtx.nonFixLHS().Identifier().isEmpty()) {
                return String.format(" (%s)", opCtx.nonFixLHS().Identifier().get(0).getText());
            }
        }
        
        return "";
    }

    private void printIndented(String text) {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < indentLevel; i++) {
            sb.append(INDENT);
        }
        sb.append(text);
        System.out.println(sb.toString());
    }
}