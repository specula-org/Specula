package printer;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import CFG.CFGFuncNode;
import CFG.CFGStmtNode;

public class CFGFuncToStr {

    private CFGFuncNode currentFunc;
    private static final CFGStmtNode EXIT = null; // Special marker for end of action

    public List<String> CFGFuncToStr(CFGFuncNode node) {
        this.currentFunc = node;
        
        List<String> res = new ArrayList<>();
        
        // Print function header: name(args) ==
        String funcname = node.getFuncName();
        List<String> argsname = node.getParameters();
        String funchead = funcname;
        if (!argsname.isEmpty()){
            funchead += "(";
            for (int i = 0; i < argsname.size(); i++) {
                funchead += argsname.get(i);
                if (i < argsname.size() - 1) {
                    funchead += ", ";
                }
            }
            funchead += ")";
        }
        funchead += " ==";
        res.add(funchead);
        
        // Call DFS to process function body and add 4-space indentation to each line
        CFGStmtNode root = node.getRoot();
        List<String> bodyLines = DFS(root, EXIT);
        for (String line : bodyLines) {
            res.add("    " + line);
        }
        
        return res;
    }

    /**
     * Core DFS algorithm implementation
     * @param entry Entry node
     * @param exit Exit node (EXIT represents end of action)
     * @return List of code lines
     */
    private List<String> DFS(CFGStmtNode entry, CFGStmtNode exit) {
        List<String> result = new ArrayList<>();
        
        if (entry == null || entry == exit) {
            return result;
        }
        
        // Handle different node types
        switch (entry.getType()) {
            case ROOT:
            case SKIP:
                // ROOT and SKIP nodes don't output content, process children directly
                return handleChildren(entry, exit);
                
            case NORMAL:
                return handleNormalStatement(entry, exit);
                
            case LET:
            case EXISTS:
            case FORALL:
                return handleBlockStatement(entry, exit);
                
            case IF_ELSE:
            case CASE:
                return handleBranchStatement(entry, exit);
                
            default:
                // Default: handle as NORMAL
                return handleNormalStatement(entry, exit);
        }
    }

    /**
     * Handle NORMAL statements (base case)
     */
    private List<String> handleNormalStatement(CFGStmtNode node, CFGStmtNode exit) {
        List<String> result = new ArrayList<>();
        
        // Add current statement content with /\ prefix
        String content = CFGNodeToStr.CFGStmtNodeToStr(node);
        if (!content.isEmpty()) {
            result.add("/\\ " + content);
        }
        
        // Recursively process children
        List<String> childResult = handleChildren(node, exit);
        result.addAll(childResult);
        
        return result;
    }

    /**
     * Handle block statements (EXISTS/FORALL/LET etc.)
     * Need to add indentation to recursive code blocks
     */
    private List<String> handleBlockStatement(CFGStmtNode node, CFGStmtNode exit) {
        List<String> result = new ArrayList<>();
        
        // Add block statement header with /\ prefix
        String content = CFGNodeToStr.CFGStmtNodeToStr(node);
        if (!content.isEmpty()) {
            result.add("/\\ " + content);
        }
        
        // Recursively process code block and add indentation
        List<String> blockResult = handleChildren(node, exit);
        for (String line : blockResult) {
            result.add("    " + line);
        }
        
        return result;
    }

    /**
     * Handle branch statements (IF/CASE/\/)
     * Find convergence points and format output
     */
    private List<String> handleBranchStatement(CFGStmtNode node, CFGStmtNode exit) {
        List<String> result = new ArrayList<>();
        
        if (node.getType() == CFGStmtNode.StmtType.IF_ELSE) {
            return handleIfStatement(node, exit);
        } else if (node.getType() == CFGStmtNode.StmtType.CASE) {
            return handleCaseStatement(node, exit);
        } else {
            // Handle disjunction (\/) and other complex branch types
            return handleGenericBranchStatement(node, exit);
        }
    }
    
    /**
     * Handle CASE statements with proper formatting:
     * /\ CASE exp ->
     *        body
     *    [] exp ->
     *        body
     *    [] OTHER ->
     *        body
     */
    private List<String> handleCaseStatement(CFGStmtNode caseNode, CFGStmtNode exit) {
        List<String> result = new ArrayList<>();
        
        // Find convergence point for all case branches
        CFGStmtNode convergencePoint = findConvergencePoint(caseNode, exit);
        
        // CASE root node should have empty content, so no header line
        
        // Process each case branch using safe "/\ " prefix checking
        List<CFGStmtNode> children = caseNode.getChildren();
        for (int i = 0; i < children.size(); i++) {
            CFGStmtNode child = children.get(i);
            List<String> branchResult = DFS(child, exit);
            
            for (int j = 0; j < branchResult.size(); j++) {
                String line = branchResult.get(j);
                
                // Safe approach: check if line starts with "/\ ", then decide what to do
                if (line.startsWith("/\\ ")) {
                    String content = line.substring(3); // Remove "/\ "
                    
                    // First line of each branch: check if it's [] or OTHER that should lose /\ prefix
                    if (j == 0 && (content.startsWith("[]") || content.startsWith("OTHER"))) {
                        // [] and OTHER branches align with CASE (3 spaces from start)
                        result.add("   " + content);
                    } else if (j == 0 && content.startsWith("CASE")) {
                        // First CASE branch gets normal /\ prefix (4 spaces from start)
                        result.add("/\\ " + content);
                    } else {
                        // Body content should be indented under CASE (7 spaces from start)
                        result.add("       /\\ " + content);
                    }
                } else {
                    // Unexpected: all lines should have /\ prefix in our system
                    throw new RuntimeException("Unexpected line without /\\ prefix in CASE: " + line);
                }
            }
        }
        
        // Continue from convergence point
        if (convergencePoint != null && convergencePoint != exit) {
            List<String> afterConvergence = DFS(convergencePoint, exit);
            result.addAll(afterConvergence);
        }
        
        return result;
    }
    
    /**
     * Handle generic branch statements (disjunctions, etc.)
     * Format with /\ prefix and \/ for each branch:
     * /\ \/ stmt
     *    \/ stmt
     */
    private List<String> handleGenericBranchStatement(CFGStmtNode node, CFGStmtNode exit) {
        List<String> result = new ArrayList<>();
        
        // Find convergence point
        CFGStmtNode convergencePoint = findConvergencePoint(node, exit);
        
        List<CFGStmtNode> children = node.getChildren();
        if (children.size() > 1) {
            // Handle multiple branches with \/ formatting for each branch
            for (int i = 0; i < children.size(); i++) {
                List<String> branchResult = DFS(children.get(i), convergencePoint);
                
                if (!branchResult.isEmpty()) {
                    String firstLine = branchResult.get(0);
                    if (i == 0) {
                        // First branch: add /\ \/ prefix
                        result.add("/\\ \\/ " + firstLine);
                    } else {
                        // Subsequent branches: add \/ prefix with alignment
                        result.add("   \\/ " + firstLine);
                    }
                    
                    // Add remaining lines from this branch with proper indentation
                    for (int j = 1; j < branchResult.size(); j++) {
                        result.add("      " + branchResult.get(j));
                    }
                }
            }
        } else {
            // Single branch, handle normally
            List<String> childResult = handleChildren(node, convergencePoint);
            result.addAll(childResult);
        }
        
        // Continue from convergence point
        if (convergencePoint != null && convergencePoint != exit) {
            List<String> afterConvergence = DFS(convergencePoint, exit);
            result.addAll(afterConvergence);
        }
        
        return result;
    }

    /**
     * Handle IF-THEN-ELSE statement with proper formatting:
     * /\ IF exp THEN
     *        body
     *        ELSE
     *        body
     */
    private List<String> handleIfStatement(CFGStmtNode ifNode, CFGStmtNode exit) {
        List<String> result = new ArrayList<>();
        
        // Get IF statement content (should be "IF condition THEN") with /\ prefix
        String ifContent = CFGNodeToStr.CFGStmtNodeToStr(ifNode);
        if (!ifContent.isEmpty()) {
            result.add("/\\ " + ifContent);
        }
        
        List<CFGStmtNode> children = ifNode.getChildren();
        if (children.size() >= 2) {
            // First child should be THEN branch
            CFGStmtNode thenNode = children.get(0);
            List<String> thenResult = DFS(thenNode, exit);
            for (String line : thenResult) {
                result.add("       " + line);  // 7 spaces
            }
            
            // Second child should be ELSE branch
            CFGStmtNode elseNode = children.get(1);
            
            // Check if ELSE node already contains "ELSE" keyword
            String elseContent = CFGNodeToStr.CFGStmtNodeToStr(elseNode);
            if (elseContent.equals("ELSE")) {
                // ELSE node is just the keyword, add it and process its children
                result.add("       ELSE");  // 7 spaces
                List<String> elseResult = handleChildren(elseNode, exit);
                for (String line : elseResult) {
                    result.add("       " + line);  // 7 spaces
                }
            } else {
                // ELSE node has content, add ELSE keyword separately
                result.add("       ELSE");  // 7 spaces
                List<String> elseResult = DFS(elseNode, exit);
                for (String line : elseResult) {
                    result.add("       " + line);  // 7 spaces
                }
            }
        }
        
        return result;
    }

    /**
     * Common method to handle children nodes
     */
    private List<String> handleChildren(CFGStmtNode node, CFGStmtNode exit) {
        List<String> result = new ArrayList<>();
        
        List<CFGStmtNode> children = node.getChildren();
        if (children.isEmpty()) {
            return result;
        }
        
        // If only one child, recurse directly
        if (children.size() == 1) {
            return DFS(children.get(0), exit);
        }
        
        // Multiple children need special handling
        // TODO: Implement multi-branch processing logic
        for (CFGStmtNode child : children) {
            List<String> childResult = DFS(child, exit);
            result.addAll(childResult);
        }
        
        return result;
    }

    /**
     * Find convergence point using post-order traversal
     * The convergence point is where all branches of a conditional statement meet again
     */
    private CFGStmtNode findConvergencePoint(CFGStmtNode branchNode, CFGStmtNode exit) {
        List<CFGStmtNode> children = branchNode.getChildren();
        if (children.size() < 2) {
            return exit; // No branching, no convergence needed
        }
        
        // Collect all reachable nodes from each branch
        Set<CFGStmtNode> firstBranchNodes = collectReachableNodes(children.get(0), exit);
        Set<CFGStmtNode> secondBranchNodes = collectReachableNodes(children.get(1), exit);
        
        // Find the first common node that both branches can reach
        // We traverse from the branch node outward to find the nearest convergence
        return findNearestCommonNode(firstBranchNodes, secondBranchNodes, exit);
    }
    
    /**
     * Collect all nodes reachable from a given node using DFS
     */
    private Set<CFGStmtNode> collectReachableNodes(CFGStmtNode start, CFGStmtNode exit) {
        Set<CFGStmtNode> reachable = new HashSet<>();
        Set<CFGStmtNode> visited = new HashSet<>();
        collectReachableNodesHelper(start, exit, reachable, visited);
        return reachable;
    }
    
    /**
     * Helper method for collecting reachable nodes
     */
    private void collectReachableNodesHelper(CFGStmtNode current, CFGStmtNode exit, 
                                           Set<CFGStmtNode> reachable, Set<CFGStmtNode> visited) {
        if (current == null || current == exit || visited.contains(current)) {
            return;
        }
        
        visited.add(current);
        reachable.add(current);
        
        List<CFGStmtNode> children = current.getChildren();
        for (CFGStmtNode child : children) {
            collectReachableNodesHelper(child, exit, reachable, visited);
        }
    }
    
    /**
     * Find the nearest common node that both sets contain
     */
    private CFGStmtNode findNearestCommonNode(Set<CFGStmtNode> firstBranch, 
                                            Set<CFGStmtNode> secondBranch, 
                                            CFGStmtNode exit) {
        // Find intersection of both sets
        Set<CFGStmtNode> commonNodes = new HashSet<>(firstBranch);
        commonNodes.retainAll(secondBranch);
        
        if (commonNodes.isEmpty()) {
            return exit; // No common nodes found, use exit
        }
        
        // For now, return the first common node found
        // In a more sophisticated implementation, we would find the "nearest" one
        // based on graph distance or control flow order
        return commonNodes.iterator().next();
    }
}
