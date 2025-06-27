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

    public CFGCALLGraph(List<CFGFuncNode> FuncNodes, List<String> variables, List<String> constants) {
        this.funcNodes = FuncNodes;
        this.callEdges = new ArrayList<>();
        this.funcNames = setupFuncNames();
        this.variables = variables;
        this.constants = constants;
    }

    public List<String> getVariables() {
        return variables;
    }

    public List<CFGCALLEdge> getCallEdges() {
        return callEdges;
    }

    public List<String> getConstants() {
        return constants;
    }


    private Set<String> setupFuncNames(){
        Set<String> funcnames = new HashSet<>();
        for (CFGFuncNode funcNode : funcNodes) {
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
        for (CFGFuncNode funcNode : funcNodes) {
            // Use HashSet to record visited nodes to avoid repeated traversal
            Set<CFGStmtNode> visited = new java.util.HashSet<>();
            
            // Start depth-first traversal from root node
            traverseStmtNode(funcNode.getRoot(), funcNode, visited);
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
                for (CFGFuncNode fn : funcNodes) {
                    if (fn.getFuncName().equals(funcName)) { // Compare original funcName
                        targetFunc = fn;
                        break;
                    }
                }
                
                if (targetFunc != null) {
                    // Create new call edge
                    CFGCALLEdge callEdge = new CFGCALLEdge(stmtNode, funcNode, targetFunc, new String[0], null);
                    addCallEdge(callEdge);
                    stmtNode.setType(CFGStmtNode.StmtType.CALL);
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
    // Get topological sort of function nodes (BFS)
    public List<CFGFuncNode> getTopologicalSort() {
        // Create in-degree table
        Map<CFGFuncNode, Integer> inDegree = new HashMap<>();
        // Create adjacency table
        Map<CFGFuncNode, List<CFGFuncNode>> adjList = new HashMap<>();
        
        // Initialize in-degree table and adjacency table
        for (CFGFuncNode node : funcNodes) {
            inDegree.put(node, 0);
            adjList.put(node, new ArrayList<>());
        }
        
        // Build in-degree table and adjacency table
        for (CFGCALLEdge edge : callEdges) {
            CFGFuncNode source = edge.getSourceFunc();
            CFGFuncNode target = edge.getTarget();
            adjList.get(source).add(target);
            inDegree.put(target, inDegree.get(target) + 1);
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
        for (CFGFuncNode funcNode : funcNodes) {
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
        funcNodes.add(funcNode);
    }

    public void addFuncName(String funcName) {
        funcNames.add(funcName);
    }

    public List<CFGFuncNode> getFuncNodes() {
        return funcNodes;
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

}
