package CFG;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;


public class CFGCALLGraph {

    // funcNodes includes all actions, funcNames only includes the first function name of undivided and divided functions
    private List<String> variables; 
    private List<String> constants;
    private List<CFGCALLEdge> callEdges;
    private List<CFGFuncNode> funcNodes;
    private Set<String> funcNames;
    // Map to store alias definitions: key is the alias name, value is the list of original variable names
    private Map<String, List<String>> aliasMap;

    public CFGCALLGraph(List<CFGFuncNode> FuncNodes, List<String> variables, List<String> constants) {
        this.funcNodes = FuncNodes;
        this.callEdges = new ArrayList<>();
        this.funcNames = setupFuncNames();
        this.variables = variables;
        this.constants = constants;
        this.aliasMap = new HashMap<>();
    }

    public List<String> getVariables() {
        return variables;
    }

    public void addVariable(String variable) {
        if (!variables.contains(variable)) {
            variables.add(variable);
        }
    }

    public List<CFGCALLEdge> getCallEdges() {
        return callEdges;
    }

    public List<String> getConstants() {
        return constants;
    }

    public Map<String, List<String>> getAliasMap() {
        return aliasMap;
    }

    public void addAlias(String alias, List<String> originalVars) {
        aliasMap.put(alias, originalVars);
    }

    public List<String> getOriginalVars(String alias) {
        return aliasMap.get(alias);
    }

    public boolean isAlias(String varName) {
        return aliasMap.containsKey(varName);
    }

    /**
     * Parse alias definitions from function nodes
     * In TLA+, alias definitions are at function level: funcname is the alias, 
     * and the first statement contains <<var1, var2, ...>>
     */
    private void parseAliasDefinitions() {
        for (CFGFuncNode funcNode : funcNodes) {
            String funcName = funcNode.getFuncName();
            CFGStmtNode root = funcNode.getRoot();
            
            // Check if this function is an alias definition
            if (root != null && root.getChildren() != null && !root.getChildren().isEmpty()) {
                CFGStmtNode firstStmt = root.getChildren().get(0);
                String content = firstStmt.getContent();
                
                // Check if the content matches alias pattern: <<var1, var2, ...>>
                if (content != null && content.trim().matches("^<<.*>>$")) {
                    List<String> originalVars = parseVariableList(content.trim());
                    if (!originalVars.isEmpty()) {
                        addAlias(funcName, originalVars);
                    }
                }
            }
        }
    }
    


    /**
     * Parse variable list from content like <<var1, var2, ...>>
     * @param content The content to parse
     * @return List of variable names
     */
    private List<String> parseVariableList(String content) {
        List<String> result = new ArrayList<>();
        
        // Remove << and >> brackets
        String innerContent = content.substring(2, content.length() - 2).trim();
        
        // Split by comma and clean up
        String[] vars = innerContent.split(",");
        for (String var : vars) {
            String cleanVar = var.trim();
            if (!cleanVar.isEmpty()) {
                result.add(cleanVar);
            }
        }
        
        return result;
    }

    /**
     * Build alias mappings by parsing function-level alias definitions
     * This method is automatically called after CFG construction in buildCallGraph()
     */
    public void buildAliasMap() {
        // Clear existing alias mappings
        aliasMap.clear();
        
        // Parse alias definitions from function nodes
        parseAliasDefinitions();
        
        // Resolve all aliases recursively
        resolveAllAliases();
    }

    /**
     * Resolve all aliases recursively and validate variables
     */
    private void resolveAllAliases() {
        // Keep resolving until no more changes
        boolean changed = true;
        int maxIterations = 100; // Prevent infinite loops
        int iterations = 0;
        
        while (changed && iterations < maxIterations) {
            changed = false;
            iterations++;
            
            // Create a copy of current alias map to avoid concurrent modification
            Map<String, List<String>> currentAliases = new HashMap<>(aliasMap);
            
            for (Map.Entry<String, List<String>> entry : currentAliases.entrySet()) {
                String aliasName = entry.getKey();
                List<String> originalVars = entry.getValue();
                List<String> resolvedVars = new ArrayList<>();
                
                for (String var : originalVars) {
                    if (isAlias(var)) {
                        // Recursive resolution
                        List<String> subVars = aliasMap.get(var);
                        if (subVars != null) {
                            resolvedVars.addAll(subVars);
                            changed = true;
                        } else {
                            resolvedVars.add(var);
                        }
                    } else {
                        resolvedVars.add(var);
                    }
                }
                
                // Update the alias map with resolved variables
                if (changed) {
                    aliasMap.put(aliasName, resolvedVars);
                }
            }
        }
        
        if (iterations >= maxIterations) {
            throw new RuntimeException("Circular alias dependencies detected or too many alias levels");
        }
        
        // Validate that all resolved variables exist in the variables list
        validateAliasVariables();
    }

    /**
     * Validate that all variables in aliases exist in the variables list
     */
    private void validateAliasVariables() {
        Set<String> variableSet = new HashSet<>(variables);
        
        for (Map.Entry<String, List<String>> entry : aliasMap.entrySet()) {
            String aliasName = entry.getKey();
            List<String> resolvedVars = entry.getValue();
            
            for (String var : resolvedVars) {
                if (!variableSet.contains(var)) {
                    throw new RuntimeException("Variable '" + var + "' in alias '" + aliasName + "' is not defined in variables list");
                }
            }
        }
    }

    /**
     * Parse alias definitions from statement content
     * Format: var == <<var1, var2, ...>>
     * @param content The statement content to parse
     */
    private void parseAliasDefinitions(String content) {
        // This method is now deprecated - keeping for backward compatibility
        // Actual alias parsing is done at function level in parseAliasDefinitions()
    }

    private Set<String> setupFuncNames(){
        Set<String> funcnames = new HashSet<>();
        for (CFGFuncNode funcNode : getAllFuncNodes()) {
            funcnames.add(funcNode.getFuncName());
        }
        return funcnames;
    }

    public Set<String> getFuncNames() {
        return this.funcNames;
    }

    public void addCallEdge(CFGCALLEdge callEdge) {
        this.callEdges.add(callEdge);
    }

    public void deleteCallEdge(CFGCALLEdge callEdge) {
        this.callEdges.remove(callEdge);
    }   

    public void buildCallGraph() {
        buildCallGraph(false);
    }
    
    public void buildCallGraph(boolean debugMode) {
        callEdges.clear();
        for (CFGFuncNode funcNode : getAllFuncNodes()) {
            // Skip alias-only functions from call graph construction
            if (funcNode.isAliasOnly()) {
                continue;
            }
            
            // Use HashSet to record visited nodes to avoid repeated traversal
            Set<CFGStmtNode> visited = new java.util.HashSet<>();
            
            // Start depth-first traversal from root node
            traverseStmtNode(funcNode.getRoot(), funcNode, visited);
        }
        
        // Automatically build alias mappings after CFG construction
        buildAliasMap();
        initializeInvocationKinds();
        
        if (debugMode) {
            printAliasMap();
        }
    }

    private void traverseStmtNode(CFGStmtNode stmtNode, CFGFuncNode funcNode, Set<CFGStmtNode> visited) {
        if (stmtNode == null || visited.contains(stmtNode)) {
            return;
        }
        visited.add(stmtNode);
        // Get current statement content
        String content = stmtNode.getContent();
        
        // Traverse all function names for matching
        for (String funcName : funcNames) {
            // (Recommended) Escape funcName to prevent it from containing regular expression meta characters
            String quotedFuncName = java.util.regex.Pattern.quote(funcName);

            // Build core regular expression pattern - function name cannot be alphanumeric underscore
            String innerPatternString = "(?<![\\w_])" + quotedFuncName + "(?![\\w_])";
            
            java.util.regex.Pattern compiledPattern = java.util.regex.Pattern.compile(innerPatternString);
            java.util.regex.Matcher matcher = compiledPattern.matcher(content);

            // Use matcher.find() to find matching
            if (matcher.find()) {
                // Find corresponding target function node
                CFGFuncNode targetFunc = null;
                for (CFGFuncNode fn : getAllFuncNodes()) {
                    if (fn.getFuncName().equals(funcName)) { // Compare original funcName
                        targetFunc = fn;
                        break;
                    }
                }
                
                if (targetFunc != null && !targetFunc.isAliasOnly()) {
                    // Create new call edge (only for non-alias functions)
                    CFGCALLEdge callEdge = new CFGCALLEdge(stmtNode, funcNode, targetFunc, new String[0], null);
                    addCallEdge(callEdge);

                    // Only set to CALL if node type is not already a structured control flow type
                    // Preserve IF_ELSE, CASE, LET, etc. types even if they contain function calls
                    CFGStmtNode.StmtType originalType = stmtNode.getType();
                    if (!isStructuredControlFlowType(originalType)) {
                        stmtNode.setType(CFGStmtNode.StmtType.CALL);
                    } else {
                        if (stmtNode.getContent() != null && stmtNode.getContent().contains("canVote")) {
                            System.err.println("DEBUG: Preserving type " + originalType + " for canVote node (not changing to CALL)");
                        }
                    }
                }
            }
        }
        
        // Recurs
        if (stmtNode.getChildren() != null) {
            for (CFGStmtNode child : stmtNode.getChildren()) {
                traverseStmtNode(child, funcNode, visited);
            }
        }
    }

    /**
     * Check if the given type is a structured control flow type that should not be overridden to CALL
     */
    private boolean isStructuredControlFlowType(CFGStmtNode.StmtType type) {
        return type == CFGStmtNode.StmtType.IF_ELSE ||
               type == CFGStmtNode.StmtType.CASE ||
               type == CFGStmtNode.StmtType.LET ||
               type == CFGStmtNode.StmtType.EXISTS ||
               type == CFGStmtNode.StmtType.FORALL ||
               type == CFGStmtNode.StmtType.CHOOSE ||
               type == CFGStmtNode.StmtType.DISJUNCTION;
    }

    private void initializeInvocationKinds() {
        for (CFGFuncNode funcNode : getAllFuncNodes()) {
            if (funcNode.isAliasOnly()) {
                continue;
            }
            funcNode.setInvocationKind(CFGFuncNode.InvocationKind.ENTRY);
        }
        for (CFGCALLEdge edge : callEdges) {
            CFGFuncNode target = edge.getTarget();
            if (target != null && !target.isAliasOnly()) {
                target.setInvocationKind(CFGFuncNode.InvocationKind.CALLED);
            }
        }
    }
    // Get topological sort of function nodes (BFS)
    public List<CFGFuncNode> getTopologicalSort() {
        // Create in-degree table
        Map<CFGFuncNode, Integer> inDegree = new HashMap<>();
        // Create adjacency table
        Map<CFGFuncNode, List<CFGFuncNode>> adjList = new HashMap<>();
        
        // Initialize in-degree table and adjacency table (exclude alias-only functions)
        for (CFGFuncNode node : getAllFuncNodes()) {
            if (!node.isAliasOnly()) {
                inDegree.put(node, 0);
                adjList.put(node, new ArrayList<>());
            }
        }
        
        // Build in-degree table and adjacency table, ignoring self-recursive calls and alias-only functions
        for (CFGCALLEdge edge : callEdges) {
            CFGFuncNode source = edge.getSourceFunc();
            CFGFuncNode target = edge.getTarget();
            
            // Ignore self-recursive calls (source calling itself)
            // Also ignore edges involving alias-only functions
            if (!source.equals(target) && !source.isAliasOnly() && !target.isAliasOnly()) {
                adjList.get(source).add(target);
                inDegree.put(target, inDegree.get(target) + 1);
            }
        }
        
        // Create queue, add nodes with in-degree 0 to queue
        Queue<CFGFuncNode> queue = new LinkedList<>();
        for (Map.Entry<CFGFuncNode, Integer> entry : inDegree.entrySet()) {
            if (entry.getValue() == 0) {
                queue.offer(entry.getKey());
            }
        }
        
        // List to store results
        List<CFGFuncNode> result = new ArrayList<>();
        
        // BFS traversal
        while (!queue.isEmpty()) {
            CFGFuncNode current = queue.poll();
            result.add(current);
            
            // Traverse all adjacent nodes of current node
            for (CFGFuncNode neighbor : adjList.get(current)) {
                // Decrease in-degree of adjacent node
                inDegree.put(neighbor, inDegree.get(neighbor) - 1);
                // If in-degree becomes 0, add to queue
                if (inDegree.get(neighbor) == 0) {
                    queue.offer(neighbor);
                }
            }
        }
        // Print topological sort result
        //  System.out.println("Topological Sort:");
        // for (CFGFuncNode node : result) {
        //     System.out.println(node.getFuncName());
        // }
        
        return result;
    }

    public List<CFGStmtNode> getStmtNodes() {
        List<CFGStmtNode> result = new ArrayList<>();
        List<CFGStmtNode> stmtNodes = new ArrayList<>();
        for (CFGFuncNode funcNode : getAllFuncNodes()) {
            stmtNodes.add(funcNode.getRoot());
        }
        while (stmtNodes.size() > 0) {
            CFGStmtNode stmtNode = stmtNodes.remove(0);
            result.add(stmtNode);
            if (stmtNode.getChildren() != null) {
                stmtNodes.addAll(stmtNode.getChildren());
            }
        }
        return result;
    }

    public List<CFGFuncNode> getTargetFunc(CFGStmtNode stmtNode) {
        List<CFGFuncNode> targetFunc = new ArrayList<>();
        for (CFGCALLEdge edge : callEdges) {
            if (edge.getSource() == stmtNode) {
                targetFunc.add(edge.getTarget());
            }
        }
        return targetFunc;
    }

    public void addFuncNode(CFGFuncNode funcNode) {
        getAllFuncNodes().add(funcNode);
    }

    public void addFuncName(String funcName) {
        funcNames.add(funcName);
    }

    /**
     * Get function nodes for analysis (excludes alias-only functions by default)
     * This is the main method used by analysis components
     * @return List of function nodes excluding alias-only functions
     */
    public List<CFGFuncNode> getFuncNodes() {
        List<CFGFuncNode> result = new ArrayList<>();
        for (CFGFuncNode funcNode : funcNodes) {
            if (!funcNode.isAliasOnly()) {
                result.add(funcNode);
            }
        }
        return result;
    }

    /**
     * Get ALL function nodes including alias-only functions
     * Use this only when you specifically need alias functions
     * @return List of all function nodes including alias-only functions
     */
    public List<CFGFuncNode> getAllFuncNodes() {
        return funcNodes;
    }

    /**
     * Get only alias-only function nodes
     * @return List of alias-only function nodes
     */
    public List<CFGFuncNode> getAliasFuncNodes() {
        List<CFGFuncNode> result = new ArrayList<>();
        for (CFGFuncNode funcNode : funcNodes) {
            if (funcNode.isAliasOnly()) {
                result.add(funcNode);
            }
        }
        return result;
    }

    public CFGFuncNode getFuncNode(String funcName) {
        for (CFGFuncNode funcNode : funcNodes) {
            if (funcNode.getFuncName().equals(funcName)) {
                return funcNode;
            }
        }
        return null;
    }

    public List<CFGCALLEdge> getCallEdgesFromStmt(CFGStmtNode stmtNode){
        List<CFGCALLEdge> result = new ArrayList<>();
        for (CFGCALLEdge edge : callEdges){
            if (edge.getSource() == stmtNode){
                result.add(edge);
            }
        }
        return result;
    }

    /**
     * Resolve aliases in a given variable name
     * If the variable is an alias, return the original variables
     * Otherwise, return a list containing the original variable name
     * @param varName The variable name to resolve
     * @return List of original variable names
     */
    public List<String> resolveAlias(String varName) {
        if (isAlias(varName)) {
            return new ArrayList<>(getOriginalVars(varName));
        } else {
            List<String> result = new ArrayList<>();
            result.add(varName);
            return result;
        }
    }

    /**
     * Get all aliases that contain a specific original variable
     * @param originalVar The original variable name
     * @return List of alias names that contain this original variable
     */
    public List<String> getAliasesContaining(String originalVar) {
        List<String> result = new ArrayList<>();
        for (Map.Entry<String, List<String>> entry : aliasMap.entrySet()) {
            if (entry.getValue().contains(originalVar)) {
                result.add(entry.getKey());
            }
        }
        return result;
    }

    /**
     * Print alias mappings for debugging
     * This method prints all alias definitions and their resolved variables
     */
    public void printAliasMap() {
        System.out.println("=== Alias Mappings ===");
        if (aliasMap.isEmpty()) {
            System.out.println("No aliases found.");
            return;
        }
        
        for (Map.Entry<String, List<String>> entry : aliasMap.entrySet()) {
            String aliasName = entry.getKey();
            List<String> resolvedVars = entry.getValue();
            
            System.out.println("Alias: " + aliasName);
            System.out.print("  -> Variables: ");
            for (int i = 0; i < resolvedVars.size(); i++) {
                System.out.print(resolvedVars.get(i));
                if (i < resolvedVars.size() - 1) {
                    System.out.print(", ");
                }
            }
            System.out.println();
        }
        System.out.println("=== End of Alias Mappings ===");
    }

    /**
     * Print detailed alias parsing information for debugging
     * This method shows the parsing process step by step
     */
    public void printAliasParsingDetails() {
        System.out.println("=== Alias Parsing Details ===");
        
        for (CFGFuncNode funcNode : funcNodes) {
            String funcName = funcNode.getFuncName();
            CFGStmtNode root = funcNode.getRoot();
            
            System.out.println("Function: " + funcName + (funcNode.isAliasOnly() ? " (alias-only)" : ""));
            
            if (root != null && root.getChildren() != null && !root.getChildren().isEmpty()) {
                CFGStmtNode firstStmt = root.getChildren().get(0);
                String content = firstStmt.getContent();
                
                System.out.println("  First statement content: " + (content != null ? content.trim() : "null"));
                
                // Check pattern <<var1, var2, ...>>
                if (content != null && content.trim().matches("^<<.*>>$")) {
                    System.out.println("  -> Matches <<...>> pattern");
                    List<String> vars = parseVariableList(content.trim());
                    System.out.println("  -> Parsed variables: " + vars);
                } else {
                    System.out.println("  -> Does not match <<...>> pattern");
                }
            } else {
                System.out.println("  -> No children or empty root");
            }
            System.out.println();
        }
        
        System.out.println("=== End of Alias Parsing Details ===");
    }

}
