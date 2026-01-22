package CFG;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Pattern;

/**
 * Variable Assignment Validation (VAV) Analyzer
 *
 * Checks TLA+ specs for variable assignment issues:
 * 1. MISSING: A variable is not assigned in some branch
 * 2. DUPLICATE: A variable is assigned multiple times in the same path
 *
 * Uses the same dataflow analysis approach as UC algorithm:
 * - InVar: variables assigned before entering a statement
 * - OutVar: variables assigned after executing a statement
 */
public class VAVAnalyzer {
    private CFGCALLGraph callGraph;
    private Set<String> variables;
    private Set<String> pureFunctions;
    private Map<CFGStmtNode, List<CFGStmtNode>> parentMap;
    private Map<String, Set<String>> funcVarChange;
    private List<String> errors;
    private boolean debugMode;

    public VAVAnalyzer(CFGCALLGraph callGraph) {
        this.callGraph = callGraph;
        this.variables = new HashSet<>(callGraph.getVariables());
        this.pureFunctions = new HashSet<>();
        this.parentMap = new HashMap<>();
        this.funcVarChange = new HashMap<>();
        this.errors = new ArrayList<>();
        this.debugMode = false;
    }

    /**
     * Validate variable assignments for all entry-point actions.
     */
    public List<String> validate() {
        errors.clear();

        // Run SA analysis first to compute InVar/OutVar and funcVarChange
        runSAAnalysis();

        // Detect pure functions AFTER SA analysis, using funcVarChange
        // A function is pure if it doesn't change any variables (including via calls)
        detectPureFunctions();

        // Then validate using the dataflow results
        for (CFGFuncNode funcNode : callGraph.getFuncNodes()) {
            if (!funcNode.isEntryPoint()) continue;
            if (funcNode.isPureExpression()) continue;  // Skip pure expression functions
            if (pureFunctions.contains(funcNode.getFuncName())) continue;

            validateFunc(funcNode);
        }

        return errors;
    }

    /**
     * Print validation results.
     */
    public void printResults(boolean debug) {
        this.debugMode = debug;
        List<String> validationErrors = validate();

        System.out.println("\n=== Variable Assignment Validation Results ===");
        if (validationErrors.isEmpty()) {
            System.out.println("No issues found. All variables are assigned exactly once in each branch.");
        } else {
            System.out.println("Found " + validationErrors.size() + " issue(s):\n");
            for (String error : validationErrors) {
                System.out.println(error);
                System.out.println();
            }
        }
        System.out.println("=== End of Validation Results ===\n");
    }

    // ============================================================================
    // SA Analysis (same as UC algorithm)
    // ============================================================================

    private void runSAAnalysis() {
        // Initialize funcVarChange for ALL functions
        List<CFGFuncNode> allFuncs = callGraph.getAllFuncNodes();
        for (CFGFuncNode funcNode : allFuncs) {
            funcVarChange.put(funcNode.getFuncName(), new HashSet<>());
        }

        // Use iterative fixed-point algorithm to propagate funcVarChange
        // This handles cases where topological sort misses some functions (e.g., cycles)
        boolean changed = true;
        int iterations = 0;
        int maxIterations = allFuncs.size() + 10; // Prevent infinite loop

        while (changed && iterations < maxIterations) {
            changed = false;
            iterations++;

            for (CFGFuncNode funcNode : allFuncs) {
                Set<String> oldVars = new HashSet<>(funcVarChange.get(funcNode.getFuncName()));
                analyzeFuncSA(funcNode);
                Set<String> newVars = funcVarChange.get(funcNode.getFuncName());

                if (!oldVars.equals(newVars)) {
                    changed = true;
                }
            }
        }

        if (debugMode) {
            System.out.println("[VAV] SA analysis converged after " + iterations + " iterations");
        }
    }

    private void analyzeFuncSA(CFGFuncNode funcNode) {
        CFGStmtNode root = funcNode.getRoot();
        if (root == null) return;

        // Build parent map for this function
        parentMap.clear();
        buildParentMap(root);

        // Initialize root's OutVar as empty
        root.OutVar = new HashSet<>();

        // Analyze children
        for (CFGStmtNode child : root.getChildren()) {
            analyzeStmtSA(funcNode, child, root.OutVar);
        }

        // Record variables changed by this function
        Set<String> leafOutVar = getAllLeafOutVar(root);
        funcVarChange.put(funcNode.getFuncName(), leafOutVar);
    }

    private void analyzeStmtSA(CFGFuncNode funcNode, CFGStmtNode stmt, Set<String> parentOutVar) {
        // InVar = parent's OutVar
        stmt.InVar = new HashSet<>(parentOutVar);

        // Get variables changed by called functions
        Set<String> calledFuncVars = new HashSet<>();
        List<CFGFuncNode> targetFuncs = callGraph.getTargetFunc(stmt);
        for (CFGFuncNode targetFunc : targetFuncs) {
            Set<String> funcVars = funcVarChange.get(targetFunc.getFuncName());
            if (funcVars != null) {
                calledFuncVars.addAll(funcVars);
            }
        }

        // Get variables changed by this statement itself
        Set<String> stmtVars = getVarsChangedByStmt(stmt);

        // OutVar = InVar + stmtVars + calledFuncVars
        stmt.OutVar = new HashSet<>(stmt.InVar);
        stmt.OutVar.addAll(stmtVars);
        stmt.OutVar.addAll(calledFuncVars);

        // Recursively analyze children
        for (CFGStmtNode child : stmt.getChildren()) {
            analyzeStmtSA(funcNode, child, stmt.OutVar);
        }
    }

    // ============================================================================
    // VAV Validation (using SA results)
    // ============================================================================

    private void validateFunc(CFGFuncNode funcNode) {
        CFGStmtNode root = funcNode.getRoot();
        if (root == null) return;

        String funcName = funcNode.getFuncName();

        if (debugMode) {
            System.out.println("\n[DEBUG] Validating function: " + funcName);
        }

        // Rebuild parent map for this function
        parentMap.clear();
        buildParentMap(root);

        // 1. Check branch convergence points (nodes with multiple parents)
        // Different branches should have the same OutVar at convergence
        for (Map.Entry<CFGStmtNode, List<CFGStmtNode>> entry : parentMap.entrySet()) {
            CFGStmtNode stmt = entry.getKey();
            List<CFGStmtNode> parents = entry.getValue();

            if (parents.size() <= 1) continue;

            // Check if all parents have consistent OutVar
            Set<String> expectedOutVar = null;
            for (CFGStmtNode parent : parents) {
                if (expectedOutVar == null) {
                    expectedOutVar = new HashSet<>(parent.OutVar);
                } else {
                    // Check for variables in one branch but not another (MISSING)
                    Set<String> diff1 = new HashSet<>(expectedOutVar);
                    diff1.removeAll(parent.OutVar);
                    Set<String> diff2 = new HashSet<>(parent.OutVar);
                    diff2.removeAll(expectedOutVar);

                    if (!diff1.isEmpty() || !diff2.isEmpty()) {
                        // Find which branch is missing variables
                        String path = getPathDescription(root, parent);
                        if (!diff1.isEmpty()) {
                            errors.add(String.format("[MISSING] %s: Branch missing variables: %s\n  Path: %s",
                                funcName, diff1, path));
                        }
                    }
                }
            }
        }

        // 2. Check leaf nodes - should have all variables assigned
        Set<String> requiredVars = new HashSet<>(variables);
        requiredVars.remove("pc");
        requiredVars.remove("stack");
        requiredVars.remove("info");

        List<CFGStmtNode> leafNodes = getAllLeafNodes(root);
        Set<String> allLeafOutVar = getAllLeafOutVar(root);

        for (int i = 0; i < leafNodes.size(); i++) {
            CFGStmtNode leaf = leafNodes.get(i);
            Set<String> missing = new HashSet<>(requiredVars);
            missing.removeAll(leaf.OutVar);

            if (!missing.isEmpty()) {
                String path = getPathDescription(root, leaf);
                errors.add(String.format("[MISSING] %s branch %d: Variables not assigned: %s\n  Path: %s",
                    funcName, i + 1, missing, path));
            }
        }

        // 3. Check for duplicate assignments (same variable assigned twice in same path)
        checkDuplicateAssignments(funcNode, root, new HashSet<>(), new HashMap<>());
    }

    private void checkDuplicateAssignments(CFGFuncNode funcNode, CFGStmtNode node,
                                           Set<CFGStmtNode> visited,
                                           Map<String, String> varAssignLocations) {
        if (node == null || visited.contains(node)) return;
        visited.add(node);

        // Get variables assigned at this node
        Set<String> varsHere = getVarsChangedByStmt(node);

        // Check for duplicates
        for (String var : varsHere) {
            if (varAssignLocations.containsKey(var)) {
                // Duplicate found
                errors.add(String.format("[DUPLICATE] %s: Variable '%s' assigned multiple times\n  First: %s\n  Second: %s",
                    funcNode.getFuncName(), var, varAssignLocations.get(var), truncate(node.getContent(), 50)));
            } else {
                varAssignLocations.put(var, truncate(node.getContent(), 50));
            }
        }

        // Handle branching: for IF-ELSE/DISJUNCTION/CASE, each branch gets its own copy
        CFGStmtNode.StmtType type = node.getType();
        if (type == CFGStmtNode.StmtType.IF_ELSE ||
            type == CFGStmtNode.StmtType.DISJUNCTION ||
            type == CFGStmtNode.StmtType.CASE) {
            // Each child is a separate branch - use separate tracking
            for (CFGStmtNode child : node.getChildren()) {
                Map<String, String> branchLocations = new HashMap<>(varAssignLocations);
                Set<CFGStmtNode> branchVisited = new HashSet<>(visited);
                checkDuplicateAssignments(funcNode, child, branchVisited, branchLocations);
            }
        } else {
            // Sequential - continue with same tracking
            for (CFGStmtNode child : node.getChildren()) {
                checkDuplicateAssignments(funcNode, child, visited, varAssignLocations);
            }
        }
    }

    // ============================================================================
    // Helper methods
    // ============================================================================

    private void detectPureFunctions() {
        // Use funcVarChange to detect pure functions
        // A function is pure if funcVarChange is empty (no variables changed, including via calls)
        pureFunctions.clear();
        for (CFGFuncNode funcNode : callGraph.getAllFuncNodes()) {
            Set<String> changedVars = funcVarChange.get(funcNode.getFuncName());
            boolean isPure = (changedVars == null || changedVars.isEmpty());

            if (isPure) {
                pureFunctions.add(funcNode.getFuncName());
                funcNode.setPureExpression(true);
            }
        }
    }

    private void buildParentMap(CFGStmtNode node) {
        if (node == null) return;
        for (CFGStmtNode child : node.getChildren()) {
            parentMap.computeIfAbsent(child, k -> new ArrayList<>()).add(node);
            buildParentMap(child);
        }
    }

    private Set<String> getVarsChangedByStmt(CFGStmtNode stmt) {
        Set<String> result = new HashSet<>();
        String content = stmt.getContent();
        if (content == null || content.isEmpty()) return result;

        // Check for prime assignments: var' = ..., var' \in ...
        for (String var : variables) {
            String primePattern = "(?<![\\w_])" + Pattern.quote(var) + "'\\s*(=|\\\\in|\\\\subseteq)";
            if (Pattern.compile(primePattern).matcher(content).find()) {
                result.add(var);
            }
        }

        // Check for UNCHANGED
        if (content.contains("UNCHANGED")) {
            Pattern listPattern = Pattern.compile("(?s)UNCHANGED\\s*<<([^<>]*)>>");
            java.util.regex.Matcher listMatcher = listPattern.matcher(content);
            while (listMatcher.find()) {
                String varsSegment = listMatcher.group(1);
                for (String candidate : varsSegment.split(",")) {
                    String trimmed = candidate.trim();
                    if (!trimmed.isEmpty()) {
                        expandAlias(trimmed, result);
                    }
                }
            }

            Pattern singlePattern = Pattern.compile("(?s)UNCHANGED\\s+(?!<<)([^\\s,]+)");
            java.util.regex.Matcher singleMatcher = singlePattern.matcher(content);
            while (singleMatcher.find()) {
                String target = singleMatcher.group(1).trim();
                if (!target.isEmpty()) {
                    expandAlias(target, result);
                }
            }
        }

        return result;
    }

    private void expandAlias(String token, Set<String> result) {
        if (variables.contains(token)) {
            result.add(token);
        } else if (callGraph.isAlias(token)) {
            List<String> resolvedVars = callGraph.resolveAlias(token);
            if (resolvedVars != null) {
                result.addAll(resolvedVars);
            }
        }
    }

    private Set<String> getAllLeafOutVar(CFGStmtNode root) {
        Set<String> result = new HashSet<>();
        for (CFGStmtNode leaf : getAllLeafNodes(root)) {
            result.addAll(leaf.OutVar);
        }
        return result;
    }

    private List<CFGStmtNode> getAllLeafNodes(CFGStmtNode node) {
        List<CFGStmtNode> result = new ArrayList<>();
        getAllLeafNodesHelper(node, result, new HashSet<>());
        return result;
    }

    private void getAllLeafNodesHelper(CFGStmtNode node, List<CFGStmtNode> result, Set<CFGStmtNode> visited) {
        if (node == null || visited.contains(node)) return;
        visited.add(node);

        if (node.getChildren().isEmpty()) {
            result.add(node);
        } else {
            for (CFGStmtNode child : node.getChildren()) {
                getAllLeafNodesHelper(child, result, visited);
            }
        }
    }

    private String getPathDescription(CFGStmtNode root, CFGStmtNode target) {
        List<String> path = new ArrayList<>();
        findPath(root, target, path, new HashSet<>());

        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < path.size() && i < 5; i++) {
            if (i > 0) sb.append(" -> ");
            sb.append(path.get(i));
        }
        if (path.size() > 5) {
            sb.append(" -> ... (").append(path.size() - 5).append(" more)");
        }
        return sb.toString();
    }

    private boolean findPath(CFGStmtNode current, CFGStmtNode target, List<String> path, Set<CFGStmtNode> visited) {
        if (current == null || visited.contains(current)) return false;
        visited.add(current);

        path.add(truncate(current.getContent(), 30));

        if (current == target) return true;

        for (CFGStmtNode child : current.getChildren()) {
            if (findPath(child, target, path, visited)) return true;
        }

        path.remove(path.size() - 1);
        return false;
    }

    private String truncate(String s, int maxLen) {
        if (s == null) return "null";
        s = s.replaceAll("\\s+", " ").trim();
        if (s.length() > maxLen) {
            return s.substring(0, maxLen) + "...";
        }
        return s;
    }
}
