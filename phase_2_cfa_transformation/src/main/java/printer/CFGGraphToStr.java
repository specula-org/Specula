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
        // 使用拓扑排序来确保调用关系正确
        Map<CFGFuncNode, Integer> inDegree = new HashMap<>();
        Map<CFGFuncNode, List<CFGFuncNode>> adjList = new HashMap<>();
        
        // 初始化入度表和邻接表
        for (CFGFuncNode node : cfg.getFuncNodes()) {
            inDegree.put(node, 0);
            adjList.put(node, new ArrayList<>());
        }
        
        // 构建入度表和邻接表
        for (CFGCALLEdge edge : cfg.getCallEdges()) {
            CFGFuncNode source = edge.getSourceFunc();
            CFGFuncNode target = edge.getTarget();
            adjList.get(source).add(target);
            inDegree.put(target, inDegree.get(target) + 1);
        }
        
        // 使用队列进行拓扑排序
        Queue<CFGFuncNode> queue = new LinkedList<>();
        for (CFGFuncNode node : cfg.getFuncNodes()) {
            if (inDegree.get(node) == 0) {
                queue.offer(node);
            }
        }
        
        // 执行拓扑排序
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
        
        // 如果存在环，则添加剩余的节点
        for (CFGFuncNode node : cfg.getFuncNodes()) {
            if (!sortedNodes.contains(node)) {
                sortedNodes.add(node);
            }
        }
        // 反转 sortedNodes
        Collections.reverse(sortedNodes);
        return sortedNodes;
    }
}
