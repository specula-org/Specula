package printer;
import java.util.List;
import java.util.ArrayList;
import java.util.Map;
import java.util.HashMap;
import java.util.Queue;
import java.util.LinkedList;
import java.util.Collections;
import CFG.CFGCALLGraph;
import CFG.CFGFuncNode;
import CFG.CFGCALLEdge;

public class CFGGraphToStr {
    public static String CFGGraphToStr(CFGCALLGraph cfg) {
        String result = "";
        List<CFGFuncNode> funcNodes = sortNodeList(cfg);
        for(CFGFuncNode node: funcNodes) {
            CFGFuncToStr funcToStr = new CFGFuncToStr();
            List<String> res = funcToStr.CFGFuncToStr(node);
            result += String.join("\n", res);
            result += "\n";
        }
        return result;
    }

    private static List<CFGFuncNode> sortNodeList(CFGCALLGraph cfg) {
        List<CFGFuncNode> sortedNodes = new ArrayList<>();
        // Use topological sort to ensure correct call relationship
        Map<CFGFuncNode, Integer> inDegree = new HashMap<>();
        Map<CFGFuncNode, List<CFGFuncNode>> adjList = new HashMap<>();
        
        // Initialize in-degree table and adjacency table
        for (CFGFuncNode node : cfg.getFuncNodes()) {
            inDegree.put(node, 0);
            adjList.put(node, new ArrayList<>());
        }
        
        // Build in-degree table and adjacency table
        for (CFGCALLEdge edge : cfg.getCallEdges()) {
            CFGFuncNode source = edge.getSourceFunc();
            CFGFuncNode target = edge.getTarget();
            adjList.get(source).add(target);
            inDegree.put(target, inDegree.get(target) + 1);
        }
        
        // Use queue for topological sort
        Queue<CFGFuncNode> queue = new LinkedList<>();
        for (CFGFuncNode node : cfg.getFuncNodes()) {
            if (inDegree.get(node) == 0) {
                queue.offer(node);
            }
        }
        
        // Execute topological sort
        while (!queue.isEmpty()) {
            CFGFuncNode current = queue.poll();
            sortedNodes.add(current);
            
            for (CFGFuncNode neighbor : adjList.get(current)) {
                inDegree.put(neighbor, inDegree.get(neighbor) - 1);
                if (inDegree.get(neighbor) == 0) {
                    queue.offer(neighbor);
                }
            }
        }
        
        // If there is a cycle, add the remaining nodes
        for (CFGFuncNode node : cfg.getFuncNodes()) {
            if (!sortedNodes.contains(node)) {
                sortedNodes.add(node);
            }
        }
        // Reverse sortedNodes
        Collections.reverse(sortedNodes);
        return sortedNodes;
    }
}
