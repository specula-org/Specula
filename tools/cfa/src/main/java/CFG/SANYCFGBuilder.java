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
    
    // Additional node types for complex expressions (corrected from AST analysis)
    private static final int N_IfThenElse = 369;
    private static final int N_Case = 336;
    private static final int N_CaseArm = 337;
    private static final int N_OtherArm = 390;
    private static final int N_LetExpr = 379;
    private static final int N_LetDef = 377;
    private static final int N_ChooseExpr = 338;
    private static final int N_SetExpr = 410;
    private static final int N_ExistsExpr = 348;
    private static final int N_ForallExpr = 355;
    
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
                } else if (stn.getKind() == N_IfThenElse) {
                    return visitIfExpression(stn);
                } else if (stn.getKind() == N_Case) {
                    return visitCaseExpression(stn);
                } else if (stn.getKind() == N_LetExpr) {
                    return visitLetExpression(stn);
                } else if (stn.getKind() == N_ChooseExpr) {
                    return visitChooseExpression(stn);
                } else if (stn.getKind() == N_SetExpr) {
                    return visitSetExpression(stn);
                } else if (stn.getKind() == N_ExistsExpr || stn.getKind() == N_ForallExpr) {
                    return visitQuantifierExpression(stn);
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
     * Visit IF-THEN-ELSE expression
     * Creates conditional branching: condition -> THEN branch, ELSE branch
     * Based on actual SANY AST structure: IF, condition, THEN, then-body, ELSE, else-body
     */
    private CFGStmtNode visitIfExpression(SyntaxTreeNode ifExprNode) {
        TreeNode[] children = ifExprNode.heirs();
        if (children == null || children.length < 6) return null;
        
        // Based on AST analysis:
        // children[0] = IF token
        // children[1] = condition expression
        // children[2] = THEN token
        // children[3] = then-body expression  
        // children[4] = ELSE token
        // children[5] = else-body expression
        
        SyntaxTreeNode conditionNode = null;
        SyntaxTreeNode thenBodyNode = null;
        SyntaxTreeNode elseBodyNode = null;
        
        if (children[1] instanceof SyntaxTreeNode) {
            conditionNode = (SyntaxTreeNode) children[1];
        }
        if (children[3] instanceof SyntaxTreeNode) {
            thenBodyNode = (SyntaxTreeNode) children[3];
        }
        if (children[5] instanceof SyntaxTreeNode) {
            elseBodyNode = (SyntaxTreeNode) children[5];
        }
        
        // Create IF statement node
        String conditionText = conditionNode != null ? reconstructExpression(conditionNode) : "unknown";
        CFGStmtNode ifStmt = new CFGStmtNode(indentationLevel, "IF " + conditionText + " THEN", ifExprNode, CFGStmtNode.StmtType.IF_ELSE);
        
        indentationLevel++;
        
        // Process THEN branch
        CFGStmtNode thenNode = new CFGStmtNode(indentationLevel, "THEN", null, CFGStmtNode.StmtType.SKIP);
        if (thenBodyNode != null) {
            CFGStmtNode thenBody = visitExpressionNode(thenBodyNode);
            if (thenBody != null) {
                thenNode.addChild(thenBody);
            }
        }
        
        // Process ELSE branch
        CFGStmtNode elseNode = new CFGStmtNode(indentationLevel, "ELSE", null, CFGStmtNode.StmtType.NORMAL);
        if (elseBodyNode != null) {
            CFGStmtNode elseBody = visitExpressionNode(elseBodyNode);
            if (elseBody != null) {
                elseNode.addChild(elseBody);
            }
        }
        
        indentationLevel--;
        
        // Connect IF statement with both branches
        ifStmt.addChild(thenNode);
        ifStmt.addChild(elseNode);
        
        return ifStmt;
    }
    
    /**
     * Visit CASE expression
     * Creates multi-way branching: condition1 -> body1, condition2 -> body2, OTHER -> default
     * Based on actual SANY AST structure: CASE, CaseArm, [], CaseArm, [], OtherArm
     */
    private CFGStmtNode visitCaseExpression(SyntaxTreeNode caseExprNode) {
        TreeNode[] children = caseExprNode.heirs();
        if (children == null || children.length == 0) return null;
        
        // Create CASE root with SKIP type for branching
        CFGStmtNode caseRoot = new CFGStmtNode(indentationLevel, "CASE", null, CFGStmtNode.StmtType.SKIP);
        
        indentationLevel++;
        
        // Process case arms and other arms
        boolean isFirst = true;
        for (TreeNode child : children) {
            if (child instanceof SyntaxTreeNode) {
                SyntaxTreeNode armNode = (SyntaxTreeNode) child;
                
                if (armNode.getKind() == N_CaseArm) {
                    // Regular case arm: condition -> body
                    CFGStmtNode caseArm = processCaseArm(armNode, isFirst);
                    if (caseArm != null) {
                        caseRoot.addChild(caseArm);
                    }
                    isFirst = false;
                } else if (armNode.getKind() == N_OtherArm) {
                    // OTHER arm: default case
                    CFGStmtNode otherArm = processOtherArm(armNode);
                    if (otherArm != null) {
                        caseRoot.addChild(otherArm);
                    }
                }
            }
        }
        
        indentationLevel--;
        
        return caseRoot;
    }
    
    /**
     * Process a single case arm
     * Based on AST structure: condition, ->, body
     */
    private CFGStmtNode processCaseArm(SyntaxTreeNode armNode, boolean isFirst) {
        TreeNode[] children = armNode.heirs();
        if (children == null || children.length < 3) return null;
        
        // Based on AST analysis:
        // children[0] = condition expression
        // children[1] = -> token
        // children[2] = body expression
        
        SyntaxTreeNode conditionNode = null;
        SyntaxTreeNode bodyNode = null;
        
        if (children[0] instanceof SyntaxTreeNode) {
            conditionNode = (SyntaxTreeNode) children[0];
        }
        if (children[2] instanceof SyntaxTreeNode) {
            bodyNode = (SyntaxTreeNode) children[2];
        }
        
        String conditionText = conditionNode != null ? reconstructExpression(conditionNode) : "unknown";
        String prefix = isFirst ? "CASE " : "[] ";
        
        CFGStmtNode caseNode = new CFGStmtNode(indentationLevel, prefix + conditionText + " ->", armNode, CFGStmtNode.StmtType.NORMAL);
        
        // Process body
        if (bodyNode != null) {
            CFGStmtNode body = visitExpressionNode(bodyNode);
            if (body != null) {
                caseNode.addChild(body);
            }
        }
        
        return caseNode;
    }
    
    /**
     * Process OTHER arm
     * Based on AST structure: OTHER, ->, body
     */
    private CFGStmtNode processOtherArm(SyntaxTreeNode otherNode) {
        TreeNode[] children = otherNode.heirs();
        if (children == null || children.length < 3) return null;
        
        // Based on AST analysis:
        // children[0] = OTHER token
        // children[1] = -> token
        // children[2] = body expression
        
        SyntaxTreeNode bodyNode = null;
        if (children[2] instanceof SyntaxTreeNode) {
            bodyNode = (SyntaxTreeNode) children[2];
        }
        
        CFGStmtNode otherArm = new CFGStmtNode(indentationLevel, "[] OTHER ->", otherNode, CFGStmtNode.StmtType.NORMAL);
        
        // Process body
        if (bodyNode != null) {
            CFGStmtNode body = visitExpressionNode(bodyNode);
            if (body != null) {
                otherArm.addChild(body);
            }
        }
        
        return otherArm;
    }
    
    /**
     * Visit LET-IN expression
     * Creates temporary variable scope: LET definitions IN body
     */
    private CFGStmtNode visitLetExpression(SyntaxTreeNode letExprNode) {
        TreeNode[] children = letExprNode.heirs();
        if (children == null || children.length < 2) return null;
        
        // Extract LET definitions and IN body
        List<String> tempVars = new ArrayList<>();
        StringBuilder letContent = new StringBuilder();
        SyntaxTreeNode inBodyNode = null;
        
        boolean inDefinitions = true;
        for (TreeNode child : children) {
            if (child instanceof SyntaxTreeNode) {
                SyntaxTreeNode stn = (SyntaxTreeNode) child;
                
                if (stn.getKind() == N_LetDef && inDefinitions) {
                    // Process LET definition
                    String defText = reconstructExpression(stn);
                    letContent.append(defText).append(" ");
                    
                    // Extract temporary variable name
                    String tempVar = extractTempVariableFromDef(stn);
                    if (tempVar != null) {
                        tempVars.add(tempVar);
                    }
                } else if (!inDefinitions) {
                    // This is the IN body
                    inBodyNode = stn;
                    break;
                } else {
                    // Transition from definitions to IN body
                    inDefinitions = false;
                    inBodyNode = stn;
                }
            }
        }
        
        // Create LET node
        String cleanedContent = letContent.toString().trim();
        CFGStmtNode letNode = new CFGStmtNode(indentationLevel, "LET " + cleanedContent + " IN", letExprNode, CFGStmtNode.StmtType.LET);
        letNode.setTemporaryVariables(tempVars);
        
        // Process IN body
        if (inBodyNode != null) {
            CFGStmtNode inBody = visitExpressionNode(inBodyNode);
            if (inBody != null) {
                letNode.addChild(inBody);
            }
        }
        
        return letNode;
    }
    
    /**
     * Visit CHOOSE expression
     * Creates non-deterministic choice: CHOOSE variable IN set : condition
     */
    private CFGStmtNode visitChooseExpression(SyntaxTreeNode chooseExprNode) {
        String chooseText = reconstructExpression(chooseExprNode);
        return new CFGStmtNode(indentationLevel, chooseText, chooseExprNode, CFGStmtNode.StmtType.NORMAL);
    }
    
    /**
     * Visit set expression
     * Creates set operations: {elements} or {x \in S : P(x)}
     */
    private CFGStmtNode visitSetExpression(SyntaxTreeNode setExprNode) {
        String setText = reconstructExpression(setExprNode);
        return new CFGStmtNode(indentationLevel, setText, setExprNode, CFGStmtNode.StmtType.NORMAL);
    }
    
    /**
     * Visit quantifier expression
     * Creates quantified expressions: \E x \in S : P(x) or \A x \in S : P(x)
     */
    private CFGStmtNode visitQuantifierExpression(SyntaxTreeNode quantExprNode) {
        String quantText = reconstructExpression(quantExprNode);
        return new CFGStmtNode(indentationLevel, quantText, quantExprNode, CFGStmtNode.StmtType.NORMAL);
    }
    
    /**
     * Generic expression node visitor - dispatches to appropriate handler
     */
    private CFGStmtNode visitExpressionNode(SyntaxTreeNode exprNode) {
        if (exprNode == null) return null;
        
        switch (exprNode.getKind()) {
            case N_ConjList:
                return visitConjunctionList(exprNode);
            case N_DisjList:
                return visitDisjunctionList(exprNode);
            case N_IfThenElse:
                return visitIfExpression(exprNode);
            case N_Case:
                return visitCaseExpression(exprNode);
            case N_LetExpr:
                return visitLetExpression(exprNode);
            case N_ChooseExpr:
                return visitChooseExpression(exprNode);
            case N_SetExpr:
                return visitSetExpression(exprNode);
            case N_ExistsExpr:
            case N_ForallExpr:
                return visitQuantifierExpression(exprNode);
            default:
                // Default: treat as normal expression
                String content = reconstructExpression(exprNode);
                return new CFGStmtNode(indentationLevel, content, exprNode, CFGStmtNode.StmtType.NORMAL);
        }
    }
    
    /**
     * Extract temporary variable name from LET definition
     */
    private String extractTempVariableFromDef(SyntaxTreeNode defNode) {
        // This is a simplified implementation
        // In practice, you'd need to parse the definition structure more carefully
        TreeNode[] children = defNode.heirs();
        if (children != null && children.length > 0) {
            return extractFirstIdentifier((SyntaxTreeNode) children[0]);
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
                // Base case: might be a complex expression (IF, CASE, etc.) or simple expression
                String operator = getOperatorFromItem(itemNode);
                
                // First try to process as complex expression (IF, CASE, LET, etc.)
                CFGStmtNode complexResult = visitExpressionNode(contentStn);
                if (complexResult != null) {
                    // Add operator prefix to the complex result
                    addOperatorPrefix(complexResult, operator);
                    return complexResult;
                } else {
                    // Fallback: treat as simple expression
                    String content = operator + " " + reconstructExpression(contentStn);
                    return new CFGStmtNode(indentationLevel, content, null, CFGStmtNode.StmtType.NORMAL);
                }
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
     * Add operator prefix to a CFG subtree
     * This recursively adds the operator prefix to the first non-SKIP, non-ROOT node
     */
    private void addOperatorPrefix(CFGStmtNode node, String operator) {
        if (node == null || operator == null || operator.isEmpty()) return;
        
        // Use a queue for BFS to find the first content node
        List<CFGStmtNode> queue = new ArrayList<>();
        queue.add(node);
        
        while (!queue.isEmpty()) {
            CFGStmtNode current = queue.remove(0);
            
            // Skip SKIP and ROOT nodes, look for the first content node
            if (current.getType() != CFGStmtNode.StmtType.SKIP && 
                current.getType() != CFGStmtNode.StmtType.ROOT) {
                // Found the first content node, add operator prefix
                current.setContent(operator + " " + current.getContent());
                break;
            }
            
            // Add children to queue
            if (current.getChildren() != null) {
                queue.addAll(current.getChildren());
            }
        }
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