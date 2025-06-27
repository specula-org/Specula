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
        // Perform DFS traversal on each node
        DFS(root, res, node);
        return res;
    }

    private void DFS(CFGStmtNode stmt, List<String> res, CFGFuncNode funcnode) {
        // If node has been visited, return
        if (!arrived.containsKey(stmt)) {
            arrived.put(stmt, true);
        } else {
            return;
        }
        // Get node content and indentation depth
        String content = CFGNodeToStr.CFGStmtNodeToStr(stmt);
        int depth = stmt.getIndentation();
        
        // Add indentation spaces based on depth
        String indentation = " ".repeat(depth * 4);
        if (content != "") {
            res.add(indentation + content);
        }
        
        // Recursively visit child nodes
        if (stmt.getChildren().size() == 1 && funcnode.getAllparents(stmt.getChildren().get(0)).size() > 1) {
            // Convergence point, can only continue visiting after all nodes before convergence point have been visited
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
            // Non-convergence point, continue DFS printing
            for (CFGStmtNode child : stmt.getChildren()) {
                DFS(child, res, funcnode);
            }
        }
    }
}
