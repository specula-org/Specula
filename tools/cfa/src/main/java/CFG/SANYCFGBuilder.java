package CFG;

import java.util.*;
import java.util.regex.Pattern;

import tla2sany.st.Location;
import tla2sany.st.TreeNode;
import tla2sany.parser.SyntaxTreeNode;
import tla2sany.semantic.*;

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
    private String originalSource;
    private int[] lineOffsets;
    private List<String> modulePrelude = new ArrayList<>();
    private List<String> modulePostlude = new ArrayList<>();
    private String moduleName;
    private static final Pattern MODULE_END_LINE_PATTERN = Pattern.compile("(?m)^\\s*====\\s*$\\R?");
    
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
    private static final int N_LetIn = 380;
    private static final int N_LetDefinitions = 379;
    private static final int N_LetExpr = 379; // Keep for backward compatibility
    private static final int N_LetDef = 377;
    private static final int N_ChooseExpr = 338;
    private static final int N_UnBoundedOrBoundedChoose = 424;
    private static final int N_MaybeBound = 381;
    private static final int N_BoundedQuant = 335;
    private static final int N_QuantBound = 408;
    private static final int N_Except = 346;
    private static final int N_ExceptSpec = 348;
    private static final int N_ExceptComponent = 347;
    private static final int N_SetExpr = 410;
    private static final int N_ExistsExpr = 348;
    private static final int N_ForallExpr = 355;
    private static final int N_UnchangedExpr = 422;
    private static final int N_PrefixExpr = 399;
    private static final int N_PostfixExpr = 395;
    private static final int N_GenPrefixOp = 362;
    private static final int N_ParamDeclaration = 392;
    private static final int N_ConsDecl = 342;
    private static final int N_IdentDecl = 363;
    private static final int N_FunctionDefinition = 356;
    
    private static final String IMAGE_BEGIN_MODULE = "N_BeginModule";
    private static final String IMAGE_END_MODULE = "N_EndModule";
    private static final Set<String> MODULE_DIRECTIVE_IMAGES = new HashSet<>(Arrays.asList(
        "N_Extends",
        "N_ModuleDefinition",
        "N_NewSymb",
        "N_UseOrHide",
        "N_Instance",
        "N_NonLocalInstance",
        "N_StructOp",
        "N_TempDecl"
    ));

    private static final Set<String> DECLARATION_PRESERVE_IMAGES = new HashSet<>(Arrays.asList(
        "N_AssumeDecl",
        "N_Assumption",
        "N_ActDecl",
        "N_Recursive",
        "N_FunctionDefinition"
    ));

    private static final Set<String> PROOF_TOLERATED_IMAGES = new HashSet<>(Arrays.asList(
        "N_Theorem",
        "N_NumberedAssumeProve",
        "N_AssumeProve"
    ));

    private static final Set<String> PROOF_REJECT_IMAGES = new HashSet<>(Arrays.asList(
        "N_Proof",
        "N_ProofStep",
        "N_ProofStatement",
        "N_ProofLet",
        "N_ProofName",
        "N_InnerProof",
        "N_LeafProof",
        "N_TerminalProof",
        "N_QEDStep",
        "N_DefStep",
        "N_HaveStep",
        "N_TakeStep",
        "N_WitnessStep",
        "N_PickStep",
        "N_CaseStep",
        "N_NumerableStep",
        "N_AssertStep",
        "N_CaseStatement",
        "N_ChooseStatement"
    ));
    
    public List<String> getVariables() { return variables; }
    public List<String> getConstants() { return constants; }
    public List<CFGFuncNode> getCfgFuncNodes() { return cfgFuncNodes; }
    public void setCfgFuncNodes(List<CFGFuncNode> nodes) {
        this.cfgFuncNodes = new ArrayList<>(nodes);
    }
    public List<String> getModulePrelude() { return Collections.unmodifiableList(modulePrelude); }
    public List<String> getModulePostlude() { return Collections.unmodifiableList(modulePostlude); }
    public String getModuleName() { return moduleName; }
    
    /**
     * Build CFG from SANY AST root node
     */
    public void buildCFG(ModuleNode moduleNode, String sourceText) {
        // Reset state
        constants = new ArrayList<>();
        variables = new ArrayList<>();
        cfgFuncNodes = new ArrayList<>();
        modulePrelude = new ArrayList<>();
        modulePostlude = new ArrayList<>();
        indentationLevel = 0;
        moduleName = moduleNode != null ? moduleNode.getName().toString() : null;
        originalSource = sourceText;
        lineOffsets = computeLineOffsets(sourceText);

        if (moduleNode == null) {
            return;
        }

        TreeNode rootNode = moduleNode.getTreeNode();
        if (rootNode instanceof SyntaxTreeNode) {
            SyntaxTreeNode stn = (SyntaxTreeNode) rootNode;
            if (stn.getKind() == N_Module) {
                visitModule(stn);
            }
        }

        // Ensure Nil is in constants (required by CFA transformation)
        if (!constants.contains("Nil")) {
            constants.add("Nil");
        }
    }
    
    private void visitModule(SyntaxTreeNode moduleNode) {
        TreeNode[] children = moduleNode.heirs();
        if (children == null) return;
        
        for (TreeNode child : children) {
            if (!(child instanceof SyntaxTreeNode)) {
                continue;
            }
            SyntaxTreeNode stn = (SyntaxTreeNode) child;
            String image = stn.getImage();

            if (IMAGE_BEGIN_MODULE.equals(image)) {
                String snippet = sanitizeModuleBeginSnippet(extractSourceFragment(stn));
                if (snippet != null && !snippet.isEmpty()) {
                    modulePrelude.add(snippet);
                }
            } else if (IMAGE_END_MODULE.equals(image)) {
                modulePostlude.add(extractSourceFragment(stn));
            } else if (image != null && MODULE_DIRECTIVE_IMAGES.contains(image)) {
                modulePrelude.add(extractSourceFragment(stn));
            } else if (image != null && PROOF_TOLERATED_IMAGES.contains(image)) {
                ensureNoRejectedProofNodes(stn);
                modulePrelude.add(extractSourceFragment(stn));
            } else if ("N_ParamDeclaration".equals(image)) {
                handleParamDeclaration(stn);
            } else if (image != null && DECLARATION_PRESERVE_IMAGES.contains(image)) {
                modulePrelude.add(extractSourceFragment(stn));
            } else if (stn.getKind() == N_Body) {
                visitBody(stn);
            } else if (image != null && PROOF_REJECT_IMAGES.contains(image)) {
                throw new UnsupportedOperationException("Proof constructs are not supported: " + image);
            }
        }
    }
    
    /**
     * Visit module body - handles declarations (variables, constants, operators)
     */
    private void visitBody(SyntaxTreeNode bodyNode) {
        TreeNode[] children = bodyNode.heirs();
        if (children == null) return;
        
        for (TreeNode child : children) {
            if (child instanceof SyntaxTreeNode) {
                SyntaxTreeNode stn = (SyntaxTreeNode) child;
                
                String image = stn.getImage();
                if (image != null && MODULE_DIRECTIVE_IMAGES.contains(image)) {
                    modulePrelude.add(extractSourceFragment(stn));
                    continue;
                }
                if (image != null && PROOF_TOLERATED_IMAGES.contains(image)) {
                    ensureNoRejectedProofNodes(stn);
                    modulePrelude.add(extractSourceFragment(stn));
                    continue;
                }
                if (image != null && PROOF_REJECT_IMAGES.contains(image)) {
                    throw new UnsupportedOperationException("Proof constructs are not supported: " + image);
                }
                if ("N_ParamDeclaration".equals(image)) {
                    handleParamDeclaration(stn);
                    continue;
                }
                if (image != null && DECLARATION_PRESERVE_IMAGES.contains(image)) {
                    modulePrelude.add(extractSourceFragment(stn));
                    continue;
                }
                
                switch (stn.getKind()) {
                    case N_VariableDeclaration:
                        visitVariableDeclaration(stn);
                        break;
                    case N_ConstantDeclaration:
                        visitConstantDeclaration(stn);
                        break;
                    case N_OperatorDefinition:
                        visitOperatorDefinition(stn);
                        break;
                    // Add other declaration types as needed
                }
            }
        }
    }
    
    private int[] computeLineOffsets(String source) {
        if (source == null) {
            return null;
        }
        List<Integer> offsets = new ArrayList<>();
        offsets.add(0);
        int length = source.length();
        for (int i = 0; i < length; i++) {
            if (source.charAt(i) == '\n') {
                offsets.add(i + 1);
            }
        }
        if (offsets.isEmpty() || offsets.get(offsets.size() - 1) != length) {
            offsets.add(length);
        }
        return offsets.stream().mapToInt(Integer::intValue).toArray();
    }

    private String extractSourceFragment(SyntaxTreeNode node) {
        if (node == null) {
            return "";
        }
        if (originalSource == null || lineOffsets == null) {
            return node.toString();
        }
        Location location = node.getLocation();
        if (location == null) {
            return node.toString();
        }

        int beginLine = Math.max(1, location.beginLine());
        int endLine = Math.max(beginLine, location.endLine());
        int lastLineIndex = Math.max(0, lineOffsets.length - 2);

        int startIdx = lineOffsets[Math.min(lastLineIndex, Math.max(0, beginLine - 1))];
        int endIdx = lineOffsets[Math.min(lineOffsets.length - 1, Math.max(0, endLine))];

        startIdx = Math.max(0, Math.min(originalSource.length(), startIdx));
        endIdx = Math.max(startIdx, Math.min(originalSource.length(), endIdx));

        return originalSource.substring(startIdx, endIdx);
    }

    private String sanitizeModuleBeginSnippet(String snippet) {
        if (snippet == null || snippet.isEmpty()) {
            return snippet;
        }
        return MODULE_END_LINE_PATTERN.matcher(snippet).replaceAll("");
    }

    private void ensureNoRejectedProofNodes(SyntaxTreeNode node) {
        if (node == null) {
            return;
        }
        Deque<TreeNode> stack = new ArrayDeque<>();
        stack.push(node);
        while (!stack.isEmpty()) {
            TreeNode current = stack.pop();
            if (!(current instanceof SyntaxTreeNode)) {
                continue;
            }
            SyntaxTreeNode stn = (SyntaxTreeNode) current;
            String image = stn.getImage();
            if (image != null && PROOF_REJECT_IMAGES.contains(image)) {
                throw new UnsupportedOperationException("Proof constructs are not supported: " + image);
            }
            TreeNode[] children = stn.heirs();
            if (children != null) {
                for (TreeNode child : children) {
                    if (child != null) {
                        stack.push(child);
                    }
                }
            }
        }
    }

    private void handleParamDeclaration(SyntaxTreeNode paramDeclNode) {
        modulePrelude.add(extractSourceFragment(paramDeclNode));
        collectConstantsFromParamDeclaration(paramDeclNode);
    }

    private void collectConstantsFromParamDeclaration(SyntaxTreeNode paramDeclNode) {
        Deque<SyntaxTreeNode> stack = new ArrayDeque<>();
        stack.push(paramDeclNode);
        while (!stack.isEmpty()) {
            SyntaxTreeNode current = stack.pop();
            if (current.getKind() == N_IdentDecl) {
                if (!identDeclHasPlaceholder(current)) {
                    String constantName = extractFirstIdentifier(current);
                    if (constantName != null && !constantName.isEmpty() && !constants.contains(constantName)) {
                        constants.add(constantName);
                    }
                }
            }
            TreeNode[] children = current.heirs();
            if (children != null) {
                for (TreeNode child : children) {
                    if (child instanceof SyntaxTreeNode) {
                        stack.push((SyntaxTreeNode) child);
                    }
                }
            }
        }
    }

    private boolean identDeclHasPlaceholder(SyntaxTreeNode identDecl) {
        TreeNode[] children = identDecl.heirs();
        if (children == null) {
            return false;
        }
        for (TreeNode child : children) {
            if (child instanceof SyntaxTreeNode) {
                String image = ((SyntaxTreeNode) child).getImage();
                if ("(".equals(image) || ")".equals(image) || "_".equals(image)) {
                    return true;
                }
            }
        }
        return false;
    }
    
    /**
     * Visit constant declaration and extract constant names
     */
    private void visitConstantDeclaration(SyntaxTreeNode constDeclNode) {
        // Extract constant names from declaration
        List<String> constNames = extractIdentifiers(constDeclNode);
        constants.addAll(constNames);
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
        
        SyntaxTreeNode bodyExprNode = extractOperatorBodyNode(opDefNode);
        CFGFuncNode cfgFuncNode = new CFGFuncNode(functionName, parameters);
        if (bodyExprNode != null) {
            cfgFuncNode.setOriginalExpression(reconstructExpression(bodyExprNode));
            CFGStmtNode bodyNode = visitExpressionNode(bodyExprNode);
            if (bodyNode != null) {
                rootNode.addChild(bodyNode);
            }
        }
        
        indentationLevel--;
        
        // Create CFGFuncNode
        cfgFuncNode.setRoot(rootNode);
        cfgFuncNodes.add(cfgFuncNode);
    }
    
    /**
     * Visit operator body - handles the actual logic statements in operator definitions
     * This method looks for the expression part after the == token and processes it
     */
    private SyntaxTreeNode extractOperatorBodyNode(SyntaxTreeNode opDefNode) {
        TreeNode[] children = opDefNode.heirs();
        if (children == null) return null;
        
        // Look for the expression part (usually after == token)
        // We need to find the actual body expression, not just the operator signature
        boolean foundEquals = false;
        for (TreeNode child : children) {
            // Skip until we find the == token or equivalent
            String tokenText = child.toString();
            if ("=".equals(tokenText) || "==".equals(tokenText) || "≜".equals(tokenText)) {
                foundEquals = true;
                continue;
            }
            
            // Process the expression after ==
            if (foundEquals && child instanceof SyntaxTreeNode) {
                return (SyntaxTreeNode) child;
            }
        }
        
        // Fallback: if no == found, try to find any expression-like node
        for (TreeNode child : children) {
            if (child instanceof SyntaxTreeNode) {
                SyntaxTreeNode stn = (SyntaxTreeNode) child;
                
                // Check if this looks like a statement or expression
                if (isStatementOrExpression(stn)) {
                    return stn;
                }
            }
        }
        
        return null;
    }
    
    /**
     * Check if a node represents a statement or expression
     */
    private boolean isStatementOrExpression(SyntaxTreeNode node) {
        int kind = node.getKind();
        return kind == N_ConjList || kind == N_DisjList || 
               kind == N_IfThenElse || kind == N_Case || 
               kind == N_LetExpr || kind == N_ChooseExpr || 
               kind == N_SetExpr || kind == N_ExistsExpr || 
               kind == N_ForallExpr || kind == N_InfixExpr || 
               kind == N_ParenExpr || kind == N_GeneralId || 
               kind == N_Number || kind == N_UnchangedExpr;
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
        
        // Create CASE root with CASE type as container for branches (empty content)
        CFGStmtNode caseRoot = new CFGStmtNode(indentationLevel, "", null, CFGStmtNode.StmtType.CASE);
        
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
        
        CFGStmtNode caseNode = new CFGStmtNode(indentationLevel, prefix + conditionText + " ->", armNode, CFGStmtNode.StmtType.CASE_ARM);
        
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
        
        CFGStmtNode otherArm = new CFGStmtNode(indentationLevel, "[] OTHER ->", otherNode, CFGStmtNode.StmtType.CASE_ARM);
        
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
     * Based on actual SANY AST structure analysis
     */
    private CFGStmtNode visitLetExpression(SyntaxTreeNode letExprNode) {
        TreeNode[] children = letExprNode.heirs();
        if (children == null || children.length < 4) return null;
        
        // Based on AST analysis:
        // children[0] = LET token
        // children[1] = N_LetDefinitions (contains all definitions)
        // children[2] = IN token
        // children[3] = body expression
        
        SyntaxTreeNode definitionsNode = null;
        SyntaxTreeNode inTokenNode = null;
        SyntaxTreeNode inBodyNode = null;

        if (children[1] instanceof SyntaxTreeNode) {
            definitionsNode = (SyntaxTreeNode) children[1];
        }
        if (children[2] instanceof SyntaxTreeNode) {
            inTokenNode = (SyntaxTreeNode) children[2];
        }
        if (children[3] instanceof SyntaxTreeNode) {
            inBodyNode = (SyntaxTreeNode) children[3];
        }
        
        // Build definitions text and extract temporary variables
        String definitionsText = "";
        List<String> tempVars = new ArrayList<>();
        
        if (definitionsNode != null) {
            definitionsText = extractSourceFragment(definitionsNode);
            if (definitionsText != null) {
                definitionsText = definitionsText.replaceAll("[ \\t\\f\\r\\n]+$", "");

                // Remove base indentation while preserving relative indentation
                String[] lines = definitionsText.split("\n", -1);
                if (lines.length > 0) {
                    // Find minimum indentation (from first line)
                    int minIndent = 0;
                    for (int i = 0; i < lines[0].length(); i++) {
                        if (lines[0].charAt(i) == ' ' || lines[0].charAt(i) == '\t') {
                            minIndent++;
                        } else {
                            break;
                        }
                    }

                    // Remove minimum indentation from all lines
                    StringBuilder normalized = new StringBuilder();
                    for (int i = 0; i < lines.length; i++) {
                        String line = lines[i];
                        if (line.length() >= minIndent) {
                            normalized.append(line.substring(minIndent));
                        } else {
                            normalized.append(line);
                        }
                        if (i < lines.length - 1) {
                            normalized.append("\n");
                        }
                    }
                    definitionsText = normalized.toString();
                }
            } else {
                definitionsText = "";
            }
            
            // Extract temporary variable names from definitions
            TreeNode[] defChildren = definitionsNode.heirs();
            if (defChildren != null) {
                for (TreeNode defChild : defChildren) {
                    if (defChild instanceof SyntaxTreeNode) {
                        SyntaxTreeNode defNode = (SyntaxTreeNode) defChild;
                        if (defNode.getKind() == N_LetDef || defNode.getKind() == N_OperatorDefinition) {
                            String tempVar = extractTempVariableFromDef(defNode);
                            if (tempVar != null && !tempVar.isEmpty()) {
                                tempVars.add(tempVar);
                            }
                        }
                    }
                }
            }
        }
        
        // Create LET node with definitions
        // Note: definitionsText already contains "LET" keyword from source (base indentation removed)
        String letContent = definitionsText;
        if (!definitionsText.endsWith("\n")) {
            letContent += "\n";
        }
        // IN should be indented 4 spaces more than LET
        letContent += "    IN";
        CFGStmtNode letNode = new CFGStmtNode(indentationLevel, letContent, letExprNode, CFGStmtNode.StmtType.LET);
        letNode.setTemporaryVariables(tempVars);

        if (letContent.contains("canVote")) {
            System.err.println("DEBUG: Created LET node with type: " + letNode.getType());
        }
        
        // Process IN body recursively
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
     * CHOOSE expressions are treated as normal expressions (like x + y)
     * They don't need special tree structure, just text reconstruction
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
     * Based on mature implementation from CFGBuilderVisitor
     */
    private CFGStmtNode visitQuantifierExpression(SyntaxTreeNode quantExprNode) {
        String quantText = reconstructExpression(quantExprNode);
        CFGStmtNode.StmtType nodeType = quantExprNode.getKind() == N_ExistsExpr ? 
            CFGStmtNode.StmtType.EXISTS : CFGStmtNode.StmtType.FORALL;
        
        CFGStmtNode quantNode = new CFGStmtNode(indentationLevel, quantText, quantExprNode, nodeType);
        
        // Extract scope information from quantifier expression
        TreeNode[] children = quantExprNode.heirs();
        if (children != null && children.length > 2) {
            // Look for the condition/scope part (usually the last child)
            for (int i = children.length - 1; i >= 0; i--) {
                if (children[i] instanceof SyntaxTreeNode) {
                    SyntaxTreeNode scopeNode = (SyntaxTreeNode) children[i];
                    CFGStmtNode scopeBody = visitExpressionNode(scopeNode);
                    if (scopeBody != null) {
                        quantNode.addChild(scopeBody);
                        break;
                    }
                }
            }
        }
        
        return quantNode;
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
            case N_LetIn:
                return visitLetExpression(exprNode);
            case N_ChooseExpr:
                return visitChooseExpression(exprNode);
            case N_SetExpr:
                return visitSetExpression(exprNode);
            case N_ExistsExpr:
            case N_ForallExpr:
                return visitQuantifierExpression(exprNode);
            default:
                // Check for UNCHANGED statements
                String content = reconstructExpression(exprNode);
                if (content.startsWith("UNCHANGED")) {
                    return new CFGStmtNode(indentationLevel, content, exprNode, CFGStmtNode.StmtType.UNCHANGED);
                }
                
                // Default: treat as normal expression
                return new CFGStmtNode(indentationLevel, content, exprNode, CFGStmtNode.StmtType.NORMAL);
        }
    }
    
    /**
     * Extract temporary variable name from LET definition
     * Based on mature implementation from CFGBuilderVisitor
     */
    private String extractTempVariableFromDef(SyntaxTreeNode defNode) {
        TreeNode[] children = defNode.heirs();
        if (children == null || children.length == 0) return null;
        
        // For operator definitions, look for IdentLHS
        for (TreeNode child : children) {
            if (child instanceof SyntaxTreeNode) {
                SyntaxTreeNode stn = (SyntaxTreeNode) child;
                
                // Check for identifier in LHS
                if (stn.getKind() == N_IdentLHS) {
                    String identifier = extractFirstIdentifier(stn);
                    if (identifier != null && !identifier.startsWith("N_")) {
                        return identifier;
                    }
                }
                
                // Check for direct identifier
                if (stn.getKind() == N_Identifier) {
                    String identifier = stn.getImage();
                    if (identifier != null && !identifier.startsWith("N_")) {
                        return identifier;
                    }
                }
            }
        }
        
        // Fallback: extract first identifier found
        return extractFirstIdentifier(defNode);
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
        CFGStmtNode disjRoot = new CFGStmtNode(indentationLevel, "DISJUNCTION_BRANCHES", null, CFGStmtNode.StmtType.DISJUNCTION);
        
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
        if (children == null || children.length == 0) return null;

        int separatorIndex = findLabelSeparator(children);
        String labelText = null;
        List<SyntaxTreeNode> candidateExprNodes = new ArrayList<>();

        if (separatorIndex >= 0) {
            labelText = normalizeLabelText(reconstructRange(children, 0, separatorIndex));
            for (int i = separatorIndex + 1; i < children.length; i++) {
                if (children[i] instanceof SyntaxTreeNode) {
                    candidateExprNodes.add((SyntaxTreeNode) children[i]);
                }
            }
        } else {
            // Original behaviour for unlabeled items
            if (children.length < 2) return null;

            TreeNode contentNode = children[1];
            if (contentNode instanceof SyntaxTreeNode) {
                SyntaxTreeNode contentStn = (SyntaxTreeNode) contentNode;

                if (contentStn.getKind() == N_ConjList) {
                    return visitConjunctionList(contentStn);
                } else if (contentStn.getKind() == N_DisjList) {
                    return visitDisjunctionList(contentStn);
                } else {
                    CFGStmtNode complexResult = visitExpressionNode(contentStn);
                    if (complexResult != null) {
                        return complexResult;
                    } else {
                        String content = reconstructExpression(contentStn);
                        return new CFGStmtNode(indentationLevel, content, null, CFGStmtNode.StmtType.NORMAL);
                    }
                }
            }
            return null;
        }

        CFGStmtNode result = null;
        for (SyntaxTreeNode candidate : candidateExprNodes) {
            if (candidate.getKind() == N_ConjList) {
                result = visitConjunctionList(candidate);
            } else if (candidate.getKind() == N_DisjList) {
                result = visitDisjunctionList(candidate);
            } else {
                result = visitExpressionNode(candidate);
            }
            if (result != null) {
                break;
            }
        }

        if (result == null) {
            // Fallback: preserve textual content and warn for future improvement
            String rawText = reconstructExpression(itemNode);
            System.err.println("WARNING: Falling back to raw text for junction item: \"" + rawText + "\"");
            return new CFGStmtNode(indentationLevel, rawText, itemNode, CFGStmtNode.StmtType.NORMAL);
        }

        if (labelText != null) {
            result.setLabel(labelText);
        }

        return result;
    }
    
    private CFGStmtNode visitConjunctionItem(SyntaxTreeNode conjItemNode) {
        return visitJunctionItem(conjItemNode);
    }

    private CFGStmtNode visitDisjunctionItem(SyntaxTreeNode disjItemNode) {
        return visitJunctionItem(disjItemNode);
    }

    private int findLabelSeparator(TreeNode[] children) {
        for (int i = 0; i < children.length; i++) {
            if (isLabelSeparator(children[i])) {
                return i;
            }
        }
        return -1;
    }

    private boolean isLabelSeparator(TreeNode node) {
        if (node == null) {
            return false;
        }
        String text = node.toString();
        return "==".equals(text);
    }

    private String normalizeLabelText(String label) {
        if (label == null) {
            return null;
        }
        String trimmed = label.trim();
        return trimmed.isEmpty() ? null : trimmed;
    }

    private String reconstructRange(TreeNode[] nodes, int startInclusive, int endExclusive) {
        StringBuilder builder = new StringBuilder();
        for (int i = startInclusive; i < endExclusive && i < nodes.length; i++) {
            TreeNode node = nodes[i];
            String fragment;
            if (node instanceof SyntaxTreeNode) {
                fragment = reconstructExpression((SyntaxTreeNode) node);
            } else {
                fragment = node != null ? node.toString() : "";
            }
            fragment = fragment == null ? "" : fragment.trim();
            if (!fragment.isEmpty()) {
                if (builder.length() > 0) {
                    builder.append(" ");
                }
                builder.append(fragment);
            }
        }
        return builder.toString();
    }
    
    
    // Removed addOperatorPrefix method - operators are now determined by printer based on CFG structure
    
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
            
            // Handle different node types with precise spacing rules
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
                    
                case N_UnBoundedOrBoundedChoose:
                    // CHOOSE variable N_MaybeBound : condition
                    TreeNode[] chooseChildren = stn.heirs();
                    if (chooseChildren != null && chooseChildren.length >= 5) {
                        // Child[0]: CHOOSE
                        reconstructExpressionRecursive(chooseChildren[0], result);
                        result.append(" ");
                        
                        // Child[1]: variable
                        reconstructExpressionRecursive(chooseChildren[1], result);
                        result.append(" ");
                        
                        // Child[2]: N_MaybeBound (contains \in and domain)
                        reconstructExpressionRecursive(chooseChildren[2], result);
                        result.append(" ");
                        
                        // Child[3]: :
                        reconstructExpressionRecursive(chooseChildren[3], result);
                        result.append(" ");
                        
                        // Child[4]: condition
                        reconstructExpressionRecursive(chooseChildren[4], result);
                    }
                    break;
                    
                case N_MaybeBound:
                    // \in domain
                    TreeNode[] maybeBoundChildren = stn.heirs();
                    if (maybeBoundChildren != null && maybeBoundChildren.length >= 2) {
                        // Child[0]: \in
                        reconstructExpressionRecursive(maybeBoundChildren[0], result);
                        result.append(" ");
                        
                        // Child[1]: domain
                        reconstructExpressionRecursive(maybeBoundChildren[1], result);
                    }
                    break;
                    
                case N_BoundedQuant:
                    // \A variable \in domain : condition
                    TreeNode[] boundedQuantChildren = stn.heirs();
                    if (boundedQuantChildren != null && boundedQuantChildren.length >= 4) {
                        // Child[0]: \A or \E
                        reconstructExpressionRecursive(boundedQuantChildren[0], result);
                        result.append(" ");
                        
                        // Child[1]: N_QuantBound
                        reconstructExpressionRecursive(boundedQuantChildren[1], result);
                        result.append(" ");
                        
                        // Child[2]: :
                        reconstructExpressionRecursive(boundedQuantChildren[2], result);
                        result.append(" ");
                        
                        // Child[3]: condition
                        reconstructExpressionRecursive(boundedQuantChildren[3], result);
                    }
                    break;
                    
                case N_QuantBound:
                    // variable \in domain
                    TreeNode[] quantBoundChildren = stn.heirs();
                    if (quantBoundChildren != null && quantBoundChildren.length >= 3) {
                        // Child[0]: variable
                        reconstructExpressionRecursive(quantBoundChildren[0], result);
                        result.append(" ");
                        
                        // Child[1]: \in
                        reconstructExpressionRecursive(quantBoundChildren[1], result);
                        result.append(" ");
                        
                        // Child[2]: domain
                        reconstructExpressionRecursive(quantBoundChildren[2], result);
                    }
                    break;
                    
                case N_Except:
                    // [identifier EXCEPT N_ExceptSpec]
                    TreeNode[] exceptChildren = stn.heirs();
                    if (exceptChildren != null && exceptChildren.length >= 5) {
                        // Child[0]: [
                        reconstructExpressionRecursive(exceptChildren[0], result);
                        
                        // Child[1]: identifier
                        reconstructExpressionRecursive(exceptChildren[1], result);
                        result.append(" ");
                        
                        // Child[2]: EXCEPT
                        reconstructExpressionRecursive(exceptChildren[2], result);
                        result.append(" ");
                        
                        // Child[3]: N_ExceptSpec (![index]=value)
                        reconstructExpressionRecursive(exceptChildren[3], result);
                        
                        // Child[4]: ]
                        reconstructExpressionRecursive(exceptChildren[4], result);
                    }
                    break;
                    
                case N_PrefixExpr:
                    // Handle all prefix expressions: operator operand
                    TreeNode[] prefixChildren = stn.heirs();
                    if (prefixChildren != null && prefixChildren.length >= 2) {
                        // Child[0]: prefix operator (UNCHANGED, ~, [], <>, etc.)
                        reconstructExpressionRecursive(prefixChildren[0], result);
                        result.append(" ");
                        
                        // Child[1]: operand
                        reconstructExpressionRecursive(prefixChildren[1], result);
                    }
                    break;
                    
                case N_IfThenElse:
                    // Handle IF-THEN-ELSE based on actual AST structure
                    TreeNode[] ifChildren = stn.heirs();
                    if (ifChildren != null && ifChildren.length >= 6) {
                        // Child[0]: IF, Child[1]: condition, Child[2]: THEN, 
                        // Child[3]: then-expr, Child[4]: ELSE, Child[5]: else-expr
                        for (int i = 0; i < ifChildren.length; i++) {
                            if (i > 0) result.append(" ");
                            reconstructExpressionRecursive(ifChildren[i], result);
                        }
                    }
                    break;
                    
                case N_LetIn:
                    // Handle LET-IN based on actual AST structure
                    TreeNode[] letChildren = stn.heirs();
                    if (letChildren != null && letChildren.length >= 4) {
                        // Child[0]: LET, Child[1]: N_LetDefinitions, Child[2]: IN, Child[3]: body
                        reconstructExpressionRecursive(letChildren[0], result); // LET
                        result.append(" ");
                        reconstructExpressionRecursive(letChildren[1], result); // definitions
                        result.append(" ");
                        reconstructExpressionRecursive(letChildren[2], result); // IN
                        result.append(" ");
                        reconstructExpressionRecursive(letChildren[3], result); // body
                    }
                    break;
                    
                case N_LetDefinitions:
                    // Handle LET definitions with proper spacing
                    TreeNode[] defChildren = stn.heirs();
                    if (defChildren != null) {
                        for (int i = 0; i < defChildren.length; i++) {
                            if (i > 0) result.append(" ");
                            reconstructExpressionRecursive(defChildren[i], result);
                        }
                    }
                    break;
                    
                case N_PostfixExpr:
                    // Handle postfix expressions without extra spaces (like y')
                    TreeNode[] postfixChildren = stn.heirs();
                    if (postfixChildren != null) {
                        for (TreeNode child : postfixChildren) {
                            reconstructExpressionRecursive(child, result);
                        }
                    }
                    break;
                    
                default:
                    // For leaf nodes and simple nodes, try to get the image
                    String image = stn.getImage();
                    if (image != null && !image.startsWith("N_")) {
                        result.append(image);
                    } else {
                        // Recursively process children with structure-based spacing
                        TreeNode[] children = stn.heirs();
                        if (children != null) {
                            processChildrenWithSpacing(children, result, stn.getKind());
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
    
    /**
     * Process children with structure-based spacing rules
     * Different node types have different spacing requirements
     */
    private void processChildrenWithSpacing(TreeNode[] children, StringBuilder result, int nodeKind) {
        TreeNode lastNonEmptyChild = null;
        
        for (int i = 0; i < children.length; i++) {
            TreeNode child = children[i];
            
            // Check if child produces any content
            StringBuilder childContent = new StringBuilder();
            reconstructExpressionRecursive(child, childContent);
            String content = childContent.toString();
            
            // Skip empty children (like empty N_IdPrefix)
            if (content.isEmpty()) {
                continue;
            }
            
            // Add spacing before child based on structure
            if (lastNonEmptyChild != null && needsSpaceBeforeChild(child, lastNonEmptyChild, nodeKind)) {
                result.append(" ");
            }
            
            result.append(content);
            lastNonEmptyChild = child;
        }
    }
    
    /**
     * Determine if space is needed before a child node
     * Based on AST node types and TLA+ syntax structure
     */
    private boolean needsSpaceBeforeChild(TreeNode currentChild, TreeNode previousChild, int parentKind) {
        if (currentChild == null || previousChild == null) {
            return false;
        }
        
        // Get node kinds for structural analysis
        int currentKind = getNodeKind(currentChild);
        int previousKind = getNodeKind(previousChild);
        
        // Check images for special tokens that don't need spaces
        String currentImage = getNodeImage(currentChild);
        String previousImage = getNodeImage(previousChild);
        
        // No space after opening brackets/parentheses
        if ("(".equals(previousImage) || "[".equals(previousImage) || "{".equals(previousImage)) {
            return false;
        }
        
        // No space before closing brackets/parentheses  
        if (")".equals(currentImage) || "]".equals(currentImage) || "}".equals(currentImage)) {
            return false;
        }
        
        // No space around operators that should be tight
        if ("!".equals(previousImage) || "!".equals(currentImage)) {
            return false;
        }
        
        // No space around field access
        if (".".equals(currentImage) || ".".equals(previousImage)) {
            return false;
        }
        
        // No space before postfix operators like ' (prime)
        if ("'".equals(currentImage)) {
            return false;
        }
        
        // For IF-THEN-ELSE and LET-IN expressions, we need spaces between tokens
        if (parentKind == N_IfThenElse || parentKind == N_LetExpr) {
            return true;
        }
        
        // Default: add space between most elements
        return true;
    }
    
    /**
     * Get node kind safely
     */
    private int getNodeKind(TreeNode node) {
        if (node instanceof SyntaxTreeNode) {
            return ((SyntaxTreeNode) node).getKind();
        }
        return -1;
    }
    
    /**
     * Get node image safely
     */
    private String getNodeImage(TreeNode node) {
        if (node instanceof SyntaxTreeNode) {
            String image = ((SyntaxTreeNode) node).getImage();
            if (image != null && !image.startsWith("N_")) {
                return image;
            }
        }
        return null;
    }
    
    /**
     * Check if text represents an operator that needs spacing around it
     * This should be based on general patterns, not hardcoded lists
     */
    private boolean isOperatorNeedingSpace(String text) {
        // This method should be redesigned to use structural patterns
        // rather than hardcoded operator lists
        return false; // Temporarily disable to remove hardcoding
    }
    
    /**
     * Check if text represents an identifier or keyword
     */
    private boolean isIdentifierOrKeyword(String text) {
        if (text == null || text.isEmpty()) return false;
        
        // Keywords
        if (text.equals("IF") || text.equals("THEN") || text.equals("ELSE") || text.equals("CASE") ||
            text.equals("LET") || text.equals("IN") || text.equals("CHOOSE") || text.equals("UNCHANGED") ||
            text.equals("EXCEPT") || text.equals("DOMAIN") || text.equals("SUBSET") || text.equals("UNION")) {
            return true;
        }
        
        // Identifiers (start with letter, contain letters/digits/underscore)
        if (Character.isLetter(text.charAt(0))) {
            return text.matches("[a-zA-Z][a-zA-Z0-9_]*");
        }
        
        return false;
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
    
    /**
     * Extract operator parameters from operator definition
     * Based on mature implementation from CFGBuilderVisitor.visitNonFixLHS
     */
    private List<String> extractOperatorParameters(SyntaxTreeNode opDefNode) {
        List<String> parameters = new ArrayList<>();
        TreeNode[] children = opDefNode.heirs();
        if (children == null) return parameters;
        
        // Look for IdentLHS which contains function name and parameters
        for (TreeNode child : children) {
            if (child instanceof SyntaxTreeNode) {
                SyntaxTreeNode stn = (SyntaxTreeNode) child;
                
                if (stn.getKind() == N_IdentLHS) {
                    // Extract all identifiers from the LHS
                    List<String> identifiers = extractIdentifiers(stn);
                    
                    // First identifier is function name, rest are parameters
                    if (identifiers.size() > 1) {
                        parameters.addAll(identifiers.subList(1, identifiers.size()));
                    }
                    break;
                }
            }
        }
        
        return parameters;
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
    
    /**
     * Visit semantic AST node (ExprNode from SANY)
     * This method bridges between SANY's semantic AST and our CFG construction
     */
    public CFGStmtNode visitExpressionNode(ExprNode exprNode, int indentLevel) {
        if (exprNode == null) return null;
        
        this.indentationLevel = indentLevel;
        
        try {
            // Handle different types of expressions
            if (exprNode instanceof OpApplNode) {
                return visitOpApplNode((OpApplNode) exprNode);
            } else if (exprNode instanceof NumeralNode) {
                return new CFGStmtNode(indentLevel, exprNode.toString(), null, CFGStmtNode.StmtType.NORMAL);
            } else if (exprNode instanceof StringNode) {
                return new CFGStmtNode(indentLevel, exprNode.toString(), null, CFGStmtNode.StmtType.NORMAL);
            } else if (exprNode instanceof DecimalNode) {
                return new CFGStmtNode(indentLevel, exprNode.toString(), null, CFGStmtNode.StmtType.NORMAL);
            } else {
                // Generic expression handling
                String content = exprNode.toString();
                return new CFGStmtNode(indentLevel, content, null, CFGStmtNode.StmtType.NORMAL);
            }
        } catch (Exception e) {
            System.err.println("Error processing expression node: " + e.getMessage());
            return new CFGStmtNode(indentLevel, "ERROR: " + exprNode.toString(), null, CFGStmtNode.StmtType.NORMAL);
        }
    }
    
    /**
     * Visit operator application node (function calls, operators, etc.)
     */
    private CFGStmtNode visitOpApplNode(OpApplNode opApplNode) {
        SymbolNode operator = opApplNode.getOperator();
        ExprOrOpArgNode[] opArgs = opApplNode.getArgs();
        
        // Convert ExprOrOpArgNode[] to ExprNode[]
        ExprNode[] args = null;
        if (opArgs != null) {
            args = new ExprNode[opArgs.length];
            for (int i = 0; i < opArgs.length; i++) {
                if (opArgs[i] instanceof ExprNode) {
                    args[i] = (ExprNode) opArgs[i];
                }
            }
        }
        
        String opName = operator.getName().toString();
        
        // Handle special operators
        switch (opName) {
            case "/\\":
                return visitConjunctionOp(args);
            case "\\/":
                return visitDisjunctionOp(args);
            case "IF":
                return visitIfThenElseOp(args);
            case "CASE":
                return visitCaseOp(args);
            case "LET":
                return visitLetOp(args);
            case "CHOOSE":
                return visitChooseOp(opApplNode);
            case "UNCHANGED":
                return visitUnchangedOp(args);
            default:
                // Regular operator application
                StringBuilder content = new StringBuilder(opName);
                if (args != null && args.length > 0) {
                    content.append("(");
                    for (int i = 0; i < args.length; i++) {
                        if (i > 0) content.append(", ");
                        content.append(args[i].toString());
                    }
                    content.append(")");
                }
                return new CFGStmtNode(indentationLevel, content.toString(), null, CFGStmtNode.StmtType.NORMAL);
        }
    }
    
    /**
     * Visit conjunction operator (/\)
     */
    private CFGStmtNode visitConjunctionOp(ExprNode[] args) {
        if (args == null || args.length == 0) return null;
        
        List<CFGStmtNode> subtrees = new ArrayList<>();
        for (ExprNode arg : args) {
            CFGStmtNode subtree = visitExpressionNode(arg, indentationLevel + 1);
            if (subtree != null) {
                // Store only pure content - printer will add /\ based on CFG structure
                subtrees.add(subtree);
            }
        }
        
        if (subtrees.isEmpty()) return null;
        if (subtrees.size() == 1) return subtrees.get(0);
        
        // Connect sequentially
        CFGStmtNode firstTree = subtrees.get(0);
        List<CFGStmtNode> currentLeaves = new ArrayList<>();
        findLeafNodes(firstTree, currentLeaves);
        
        for (int i = 1; i < subtrees.size(); i++) {
            CFGStmtNode nextTree = subtrees.get(i);
            for (CFGStmtNode leaf : currentLeaves) {
                leaf.addChild(nextTree);
            }
            currentLeaves.clear();
            findLeafNodes(nextTree, currentLeaves);
        }
        
        return firstTree;
    }
    
    /**
     * Visit disjunction operator (\/)
     */
    private CFGStmtNode visitDisjunctionOp(ExprNode[] args) {
        if (args == null || args.length == 0) return null;
        
        List<CFGStmtNode> subtrees = new ArrayList<>();
        for (ExprNode arg : args) {
            CFGStmtNode subtree = visitExpressionNode(arg, indentationLevel + 1);
            if (subtree != null) {
                // Store only pure content - printer will add \/ based on CFG structure
                subtrees.add(subtree);
            }
        }
        
        if (subtrees.isEmpty()) return null;
        if (subtrees.size() == 1) return subtrees.get(0);
        
        // Create parallel branches
        CFGStmtNode disjRoot = new CFGStmtNode(indentationLevel, "DISJUNCTION_BRANCHES", null, CFGStmtNode.StmtType.DISJUNCTION);
        for (CFGStmtNode subtree : subtrees) {
            disjRoot.addChild(subtree);
        }
        
        return disjRoot;
    }
    
    /**
     * Visit IF-THEN-ELSE operator
     */
    private CFGStmtNode visitIfThenElseOp(ExprNode[] args) {
        if (args == null || args.length < 3) return null;
        
        String condition = args[0].toString();
        CFGStmtNode ifNode = new CFGStmtNode(indentationLevel, "IF " + condition + " THEN", null, CFGStmtNode.StmtType.IF_ELSE);
        
        // THEN branch
        CFGStmtNode thenNode = new CFGStmtNode(indentationLevel + 1, "THEN", null, CFGStmtNode.StmtType.SKIP);
        CFGStmtNode thenBody = visitExpressionNode(args[1], indentationLevel + 2);
        if (thenBody != null) {
            thenNode.addChild(thenBody);
        }
        
        // ELSE branch
        CFGStmtNode elseNode = new CFGStmtNode(indentationLevel + 1, "ELSE", null, CFGStmtNode.StmtType.NORMAL);
        CFGStmtNode elseBody = visitExpressionNode(args[2], indentationLevel + 2);
        if (elseBody != null) {
            elseNode.addChild(elseBody);
        }
        
        ifNode.addChild(thenNode);
        ifNode.addChild(elseNode);
        
        return ifNode;
    }
    
    /**
     * Visit CASE operator
     */
    private CFGStmtNode visitCaseOp(ExprNode[] args) {
        System.out.println("DEBUG visitCaseOp: Creating CASE node with " + (args != null ? args.length : 0) + " args");
        CFGStmtNode caseNode = new CFGStmtNode(indentationLevel, "CASE", null, CFGStmtNode.StmtType.CASE);
        
        // Process case arms
        if (args != null) {
            for (int i = 0; i < args.length; i += 2) {
                if (i + 1 < args.length) {
                    String condition = args[i].toString();
                    System.out.println("DEBUG visitCaseOp: Creating CASE_ARM with condition: " + condition);
                    CFGStmtNode armNode = new CFGStmtNode(indentationLevel + 1, condition + " ->", null, CFGStmtNode.StmtType.CASE_ARM);
                    CFGStmtNode armBody = visitExpressionNode(args[i + 1], indentationLevel + 2);
                    if (armBody != null) {
                        armNode.addChild(armBody);
                    }
                    caseNode.addChild(armNode);
                    System.out.println("DEBUG visitCaseOp: Added CASE_ARM to caseNode, type = " + armNode.getType());
                }
            }
        }
        
        System.out.println("DEBUG visitCaseOp: Returning CASE node with " + caseNode.getChildren().size() + " children");
        return caseNode;
    }
    
    /**
     * Visit LET operator
     */
    private CFGStmtNode visitLetOp(ExprNode[] args) {
        CFGStmtNode letNode = new CFGStmtNode(indentationLevel, "LET ... IN", null, CFGStmtNode.StmtType.LET);
        
        // Process LET body (usually the last argument)
        if (args != null && args.length > 0) {
            CFGStmtNode body = visitExpressionNode(args[args.length - 1], indentationLevel + 1);
            if (body != null) {
                letNode.addChild(body);
            }
        }
        
        return letNode;
    }
    
    /**
     * Visit CHOOSE operator
     */
    private CFGStmtNode visitChooseOp(OpApplNode chooseNode) {
        String content = "CHOOSE " + chooseNode.toString();
        return new CFGStmtNode(indentationLevel, content, null, CFGStmtNode.StmtType.NORMAL);
    }
    
    /**
     * Visit UNCHANGED operator
     */
    private CFGStmtNode visitUnchangedOp(ExprNode[] args) {
        StringBuilder content = new StringBuilder("UNCHANGED");
        if (args != null && args.length > 0) {
            content.append(" ");
            for (int i = 0; i < args.length; i++) {
                if (i > 0) content.append(", ");
                content.append(args[i].toString());
            }
        }
        return new CFGStmtNode(indentationLevel, content.toString(), null, CFGStmtNode.StmtType.UNCHANGED);
    }
}
