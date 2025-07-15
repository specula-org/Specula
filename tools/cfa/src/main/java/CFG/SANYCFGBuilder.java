package CFG;

import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import tla2sany.st.TreeNode;
import tla2sany.parser.SyntaxTreeNode;

/**
 * CFG Builder using SANY AST instead of ANTLR
 * Builds control flow graph from TLA+ specifications parsed by TLC's SANY parser
 */
public class SANYCFGBuilder {
    private static final String IGNORE_OPERATORS = "^(Init|Next|Spec|TypeOK|TypeInvariant)";
    private List<String> constants = new ArrayList<>();
    private List<String> variables = new ArrayList<>();
    private List<CFGFuncNode> cfgFuncNodes = new ArrayList<>();
    private int indentationLevel = 0;
    
    // SANY AST node kind constants
    private static final int N_Module = 382;
    private static final int N_Body = 334;
    private static final int N_OperatorDefinition = 389;
    private static final int N_VariableDeclaration = 426;
    private static final int N_ConstantDeclaration = 327; // Approximate
    private static final int N_ConjList = 341;
    private static final int N_DisjList = 344;
    private static final int N_ConjItem = 340;
    private static final int N_DisjItem = 343;
    private static final int N_InfixExpr = 371;
    private static final int N_GeneralId = 358;
    private static final int N_Number = 385;
    private static final int N_Identifier = 289;
    private static final int N_IdentLHS = 366;
    private static final int N_ParenExpr = 393;
    
    public List<String> getVariables() { return variables; }
    public List<String> getConstants() { return constants; }
    public List<CFGFuncNode> getCfgFuncNodes() { return cfgFuncNodes; }
    
    /**
     * Build CFG from SANY AST root node
     */
    public void buildCFG(TreeNode rootNode) {
        if (rootNode instanceof SyntaxTreeNode) {
            SyntaxTreeNode stn = (SyntaxTreeNode) rootNode;
            if (stn.getKind() == N_Module) {
                visitModule(stn);
            }
        }
    }
    
    private void visitModule(SyntaxTreeNode moduleNode) {
        TreeNode[] children = moduleNode.heirs();
        if (children == null) return;
        
        for (TreeNode child : children) {
            if (child instanceof SyntaxTreeNode) {
                SyntaxTreeNode stn = (SyntaxTreeNode) child;
                if (stn.getKind() == N_Body) {
                    visitBody(stn);
                }
            }
        }
    }
    
    private void visitBody(SyntaxTreeNode bodyNode) {
        TreeNode[] children = bodyNode.heirs();
        if (children == null) return;
        
        for (TreeNode child : children) {
            if (child instanceof SyntaxTreeNode) {
                SyntaxTreeNode stn = (SyntaxTreeNode) child;
                
                switch (stn.getKind()) {
                    case N_VariableDeclaration:
                        visitVariableDeclaration(stn);
                        break;
                    case N_OperatorDefinition:
                        visitOperatorDefinition(stn);
                        break;
                    // Add other declaration types as needed
                }
            }
        }
    }
    
    private void visitVariableDeclaration(SyntaxTreeNode varDeclNode) {
        // Extract variable names from declaration
        List<String> varNames = extractIdentifiers(varDeclNode);
        variables.addAll(varNames);
    }
    
    private void visitOperatorDefinition(SyntaxTreeNode opDefNode) {
        // Extract function name and parameters
        String functionName = extractOperatorName(opDefNode);
        List<String> parameters = extractOperatorParameters(opDefNode);
        
        // Check if this is an operator we should ignore
        Pattern ignorePattern = Pattern.compile(IGNORE_OPERATORS);
        if (ignorePattern.matcher(functionName).find()) {
            return;
        }
        
        // Create root CFG node
        CFGStmtNode rootNode = new CFGStmtNode(indentationLevel, "root", null, CFGStmtNode.StmtType.ROOT);
        
        indentationLevel++;
        
        // Find and process the operator body
        CFGStmtNode bodyNode = visitOperatorBody(opDefNode);
        if (bodyNode != null) {
            rootNode.addChild(bodyNode);
        }
        
        indentationLevel--;
        
        // Create CFGFuncNode
        CFGFuncNode cfgFuncNode = new CFGFuncNode(functionName, parameters);
        cfgFuncNode.setRoot(rootNode);
        cfgFuncNodes.add(cfgFuncNode);
    }
    
    private CFGStmtNode visitOperatorBody(SyntaxTreeNode opDefNode) {
        TreeNode[] children = opDefNode.heirs();
        if (children == null) return null;
        
        // Look for the expression part (usually the last child after == token)
        for (TreeNode child : children) {
            if (child instanceof SyntaxTreeNode) {
                SyntaxTreeNode stn = (SyntaxTreeNode) child;
                
                // Check if this is a junction list
                if (stn.getKind() == N_ConjList) {
                    return visitConjunctionList(stn);
                } else if (stn.getKind() == N_DisjList) {
                    return visitDisjunctionList(stn);
                } else if (stn.getKind() == N_InfixExpr || stn.getKind() == N_ParenExpr) {
                    // Single expression
                    String content = reconstructExpression(stn);
                    return new CFGStmtNode(indentationLevel, content, stn, CFGStmtNode.StmtType.NORMAL);
                }
            }
        }
        
        return null;
    }
    
    /**
     * Visit conjunction list (/\\ statements)
     * Creates sequential execution: stmt1 -> stmt2 -> stmt3
     * Each item can be a nested junction list (recursive)
     */
    private CFGStmtNode visitConjunctionList(SyntaxTreeNode conjListNode) {
        TreeNode[] items = conjListNode.heirs();
        if (items == null || items.length == 0) return null;
        
        // Recursively process each conjunction item to get subtrees
        List<CFGStmtNode> subtrees = new ArrayList<>();
        
        for (TreeNode item : items) {
            if (item instanceof SyntaxTreeNode) {
                SyntaxTreeNode conjItem = (SyntaxTreeNode) item;
                if (conjItem.getKind() == N_ConjItem) {
                    CFGStmtNode subtree = visitJunctionItem(conjItem);
                    if (subtree != null) {
                        subtrees.add(subtree);
                    }
                }
            }
        }
        
        if (subtrees.isEmpty()) {
            return null;
        }
        
        // If only one subtree, return it directly
        if (subtrees.size() == 1) {
            return subtrees.get(0);
        }
        
        // Connect subtrees sequentially: leaves of tree[i] -> root of tree[i+1]
        CFGStmtNode firstTree = subtrees.get(0);
        List<CFGStmtNode> currentLeaves = new ArrayList<>();
        findLeafNodes(firstTree, currentLeaves);
        
        for (int i = 1; i < subtrees.size(); i++) {
            CFGStmtNode nextTree = subtrees.get(i);
            
            // Connect all current leaves to the root of next tree
            for (CFGStmtNode leaf : currentLeaves) {
                leaf.addChild(nextTree);
            }
            
            // Update current leaves to be the leaves of the newly connected tree
            currentLeaves.clear();
            findLeafNodes(nextTree, currentLeaves);
        }
        
        return firstTree;
    }
    
    /**
     * Visit disjunction list (\\/ statements)  
     * Creates branching execution: all branches should be parallel alternatives
     * Supports recursive junction items (each item can be a nested junction list)
     */
    private CFGStmtNode visitDisjunctionList(SyntaxTreeNode disjListNode) {
        TreeNode[] items = disjListNode.heirs();
        if (items == null || items.length == 0) return null;
        
        // Recursively process each disjunction item to get subtrees
        List<CFGStmtNode> subtrees = new ArrayList<>();
        
        for (TreeNode item : items) {
            if (item instanceof SyntaxTreeNode) {
                SyntaxTreeNode disjItem = (SyntaxTreeNode) item;
                if (disjItem.getKind() == N_DisjItem) {
                    CFGStmtNode subtree = visitJunctionItem(disjItem);
                    if (subtree != null) {
                        subtrees.add(subtree);
                    }
                }
            }
        }
        
        if (subtrees.isEmpty()) {
            return null;
        }
        
        // If only one subtree, return it directly
        if (subtrees.size() == 1) {
            return subtrees.get(0);
        }
        
        // For multiple subtrees, create a SKIP-type virtual root that branches to all subtrees
        // This represents true parallel execution branches
        CFGStmtNode disjRoot = new CFGStmtNode(indentationLevel, "DISJUNCTION_BRANCHES", null, CFGStmtNode.StmtType.SKIP);
        
        // Add all subtrees as parallel branches (no sequential connection)
        for (CFGStmtNode subtree : subtrees) {
            disjRoot.addChild(subtree);
        }
        
        return disjRoot;
    }
    
    /**
     * Visit junction item - can be either a simple expression or a nested junction list
     * This is the key recursive method that handles nested structures
     */
    private CFGStmtNode visitJunctionItem(SyntaxTreeNode itemNode) {
        TreeNode[] children = itemNode.heirs();
        if (children == null || children.length < 2) return null;
        
        // First child is the operator (/\\ or \\/), second is the content
        TreeNode contentNode = children[1];
        
        if (contentNode instanceof SyntaxTreeNode) {
            SyntaxTreeNode contentStn = (SyntaxTreeNode) contentNode;
            
            // Check if the content is itself a junction list (recursive case)
            if (contentStn.getKind() == N_ConjList) {
                return visitConjunctionList(contentStn);
            } else if (contentStn.getKind() == N_DisjList) {
                return visitDisjunctionList(contentStn);
            } else {
                // Base case: regular expression
                String operator = getOperatorFromItem(itemNode);
                String content = operator + " " + reconstructExpression(contentStn);
                return new CFGStmtNode(indentationLevel, content, null, CFGStmtNode.StmtType.NORMAL);
            }
        }
        
        return null;
    }
    
    private CFGStmtNode visitConjunctionItem(SyntaxTreeNode conjItemNode) {
        return visitJunctionItem(conjItemNode);
    }
    
    private CFGStmtNode visitDisjunctionItem(SyntaxTreeNode disjItemNode) {
        return visitJunctionItem(disjItemNode);
    }
    
    /**
     * Helper method to extract operator from junction item node
     */
    private String getOperatorFromItem(SyntaxTreeNode itemNode) {
        if (itemNode.getKind() == N_ConjItem) {
            return "/\\";
        } else if (itemNode.getKind() == N_DisjItem) {
            return "\\/";
        }
        return "";
    }
    
    /**
     * Reconstruct expression text from SANY AST
     */
    private String reconstructExpression(SyntaxTreeNode exprNode) {
        StringBuilder result = new StringBuilder();
        reconstructExpressionRecursive(exprNode, result);
        return result.toString().trim();
    }
    
    private void reconstructExpressionRecursive(TreeNode node, StringBuilder result) {
        if (node instanceof SyntaxTreeNode) {
            SyntaxTreeNode stn = (SyntaxTreeNode) node;
            
            // Handle different node types
            switch (stn.getKind()) {
                case N_ParenExpr:
                    result.append("(");
                    TreeNode[] parenChildren = stn.heirs();
                    if (parenChildren != null && parenChildren.length > 1) {
                        // Skip first and last children (parentheses), process middle
                        for (int i = 1; i < parenChildren.length - 1; i++) {
                            reconstructExpressionRecursive(parenChildren[i], result);
                        }
                    }
                    result.append(")");
                    break;
                    
                case N_InfixExpr:
                    TreeNode[] infixChildren = stn.heirs();
                    if (infixChildren != null && infixChildren.length >= 3) {
                        reconstructExpressionRecursive(infixChildren[0], result); // left operand
                        result.append(" ");
                        reconstructExpressionRecursive(infixChildren[1], result); // operator
                        result.append(" ");
                        reconstructExpressionRecursive(infixChildren[2], result); // right operand
                    }
                    break;
                    
                default:
                    // For leaf nodes and simple nodes, try to get the image
                    String image = stn.getImage();
                    if (image != null && !image.startsWith("N_")) {
                        result.append(image);
                    } else {
                        // Recursively process children
                        TreeNode[] children = stn.heirs();
                        if (children != null) {
                            for (TreeNode child : children) {
                                reconstructExpressionRecursive(child, result);
                                result.append(" ");
                            }
                        }
                    }
                    break;
            }
        } else {
            // Non-SyntaxTreeNode, just get string representation
            String text = node.toString();
            if (text != null && !text.startsWith("N_")) {
                result.append(text);
            }
        }
    }
    
    // Utility methods
    private String extractOperatorName(SyntaxTreeNode opDefNode) {
        TreeNode[] children = opDefNode.heirs();
        if (children == null) return "unknown";
        
        for (TreeNode child : children) {
            if (child instanceof SyntaxTreeNode) {
                SyntaxTreeNode stn = (SyntaxTreeNode) child;
                if (stn.getKind() == N_IdentLHS) {
                    // Find the identifier in the LHS
                    return extractFirstIdentifier(stn);
                }
            }
        }
        
        return "unknown";
    }
    
    private List<String> extractOperatorParameters(SyntaxTreeNode opDefNode) {
        // For now, return empty list - parameters extraction would need more complex logic
        return new ArrayList<>();
    }
    
    private List<String> extractIdentifiers(SyntaxTreeNode node) {
        List<String> identifiers = new ArrayList<>();
        extractIdentifiersRecursive(node, identifiers);
        return identifiers;
    }
    
    private void extractIdentifiersRecursive(TreeNode node, List<String> identifiers) {
        if (node instanceof SyntaxTreeNode) {
            SyntaxTreeNode stn = (SyntaxTreeNode) node;
            
            if (stn.getKind() == N_Identifier) {
                String image = stn.getImage();
                if (image != null && !image.startsWith("N_")) {
                    identifiers.add(image);
                }
            }
            
            TreeNode[] children = stn.heirs();
            if (children != null) {
                for (TreeNode child : children) {
                    extractIdentifiersRecursive(child, identifiers);
                }
            }
        }
    }
    
    private String extractFirstIdentifier(SyntaxTreeNode node) {
        if (node instanceof SyntaxTreeNode) {
            SyntaxTreeNode stn = (SyntaxTreeNode) node;
            
            if (stn.getKind() == N_Identifier) {
                return stn.getImage();
            }
            
            TreeNode[] children = stn.heirs();
            if (children != null) {
                for (TreeNode child : children) {
                    String identifier = extractFirstIdentifier((SyntaxTreeNode) child);
                    if (identifier != null && !identifier.startsWith("N_")) {
                        return identifier;
                    }
                }
            }
        }
        
        return null;
    }
    
    private void findLeafNodes(CFGStmtNode node, List<CFGStmtNode> leaves) {
        if (node == null) return;
        
        if (node.getChildren().isEmpty()) {
            leaves.add(node);
        } else {
            for (CFGStmtNode child : node.getChildren()) {
                findLeafNodes(child, leaves);
            }
        }
    }
}