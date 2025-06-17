package printer;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import CFG.CFGFuncNode;
import CFG.CFGStmtNode;

public class CFGFuncToStr {

    private Map<CFGStmtNode, Boolean> arrived = new HashMap<>();

    public List<String> CFGFuncToStr(CFGFuncNode node) {
        List<String> res = new ArrayList<>();
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
        CFGStmtNode root = node.getRoot();
        // 对每个节点进行DFS遍历
        DFS(root, res, node);
        return res;
    }

    private void DFS(CFGStmtNode stmt, List<String> res, CFGFuncNode funcnode) {
        // 如果节点已访问过则返回
        if (!arrived.containsKey(stmt)) {
            arrived.put(stmt, true);
        } else {
            return;
        }
        // 获取节点内容和缩进深度
        String content = CFGNodeToStr.CFGStmtNodeToStr(stmt);
        int depth = stmt.getIndentation();
        
        // 根据深度添加缩进空格
        String indentation = " ".repeat(depth * 4);
        if (content != "") {
            res.add(indentation + content);
        }
        
        // 递归访问子节点
        if (stmt.getChildren().size() == 1 && funcnode.getAllparents(stmt.getChildren().get(0)).size() > 1) {
            // 汇聚点，只有汇聚点前所有节点都被访问后才能继续访问
            CFGStmtNode convergence_node = stmt.getChildren().get(0);
            Set<CFGStmtNode> parents = funcnode.getAllparents(convergence_node);
            int count = 0;
            for (CFGStmtNode parent: parents){
                if (arrived.containsKey(parent) && arrived.get(parent)){
                    count++;
                }
            }
            if (count == parents.size()){
                DFS(convergence_node, res, funcnode);
            }
        } else {
            //非汇聚点，继续 DFS 打印
            for (CFGStmtNode child : stmt.getChildren()) {
                DFS(child, res, funcnode);
            }
        }
    }
}
