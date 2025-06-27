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
    // funcNodes 包括所有动作，funcNames 只包括未分割的和分割后的第一个函数名
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
            // 使用HashSet记录已访问过的节点,避免重复遍历
            Set<CFGStmtNode> visited = new java.util.HashSet<>();
            
            // 从根节点开始深度优先遍历
            traverseStmtNode(funcNode.getRoot(), funcNode, visited);
        }
    }

    private void traverseStmtNode(CFGStmtNode stmtNode, CFGFuncNode funcNode, Set<CFGStmtNode> visited) {
        if (stmtNode == null || visited.contains(stmtNode)) {
            return;
        }
        visited.add(stmtNode);
        // 获取当前语句内容
        String content = stmtNode.getContent();
        
        // 遍历所有函数名进行匹配
        for (String funcName : funcNames) {
            // (推荐) 对 funcName 进行转义，以防其包含正则表达式元字符
            String quotedFuncName = java.util.regex.Pattern.quote(funcName);

            // 构建核心的正则表达式模式 - 函数名前后不能是字母数字下划线
            String innerPatternString = "(?<![\\w_])" + quotedFuncName + "(?![\\w_])";
            
            java.util.regex.Pattern compiledPattern = java.util.regex.Pattern.compile(innerPatternString);
            java.util.regex.Matcher matcher = compiledPattern.matcher(content);

            // 使用 matcher.find() 来查找匹配
            if (matcher.find()) {
                // 找到对应的目标函数节点
                CFGFuncNode targetFunc = null;
                for (CFGFuncNode fn : funcNodes) {
                    if (fn.getFuncName().equals(funcName)) { // 比较原始的 funcName
                        targetFunc = fn;
                        break;
                    }
                }
                
                if (targetFunc != null) {
                    // 创建新的调用边
                    CFGCALLEdge callEdge = new CFGCALLEdge(stmtNode, funcNode, targetFunc, new String[0], null);
                    addCallEdge(callEdge);
                    stmtNode.setType(CFGStmtNode.StmtType.CALL);
                }
            }
        }
        
        // 递归遍历子节点
        if (stmtNode.getChildren() != null) {
            for (CFGStmtNode child : stmtNode.getChildren()) {
                traverseStmtNode(child, funcNode, visited);
            }
        }
    }
    // 获得拓函数节点的拓扑排序 (BFS)
    public List<CFGFuncNode> getTopologicalSort() {
        // 创建入度表
        Map<CFGFuncNode, Integer> inDegree = new HashMap<>();
        // 创建邻接表
        Map<CFGFuncNode, List<CFGFuncNode>> adjList = new HashMap<>();
        
        // 初始化入度表和邻接表
        for (CFGFuncNode node : funcNodes) {
            inDegree.put(node, 0);
            adjList.put(node, new ArrayList<>());
        }
        
        // 构建入度表和邻接表
        for (CFGCALLEdge edge : callEdges) {
            CFGFuncNode source = edge.getSourceFunc();
            CFGFuncNode target = edge.getTarget();
            adjList.get(source).add(target);
            inDegree.put(target, inDegree.get(target) + 1);
        }
        
        // 创建队列,将入度为0的节点加入队列
        Queue<CFGFuncNode> queue = new LinkedList<>();
        for (Map.Entry<CFGFuncNode, Integer> entry : inDegree.entrySet()) {
            if (entry.getValue() == 0) {
                queue.offer(entry.getKey());
            }
        }
        
        // 存储结果的列表
        List<CFGFuncNode> result = new ArrayList<>();
        
        // BFS遍历
        while (!queue.isEmpty()) {
            CFGFuncNode current = queue.poll();
            result.add(current);
            
            // 遍历当前节点的所有邻接节点
            for (CFGFuncNode neighbor : adjList.get(current)) {
                // 将邻接节点的入度减1
                inDegree.put(neighbor, inDegree.get(neighbor) - 1);
                // 如果入度变为0,加入队列
                if (inDegree.get(neighbor) == 0) {
                    queue.offer(neighbor);
                }
            }
        }
        // 打印拓扑排序结果
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
