package CFG;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class CFGFuncNode {
    private String funcName;  // 函数名
    private List<String> parameters;  // 函数参数列表
    private CFGStmtNode root;  // 函数体语句节点列表 
    private int id;
    private Map<CFGStmtNode, Boolean> arrived;

    // 构造函数
    public CFGFuncNode(String funcName, List<String> parameters) {
        this.funcName = funcName;
        this.parameters = parameters;
        this.root = null;
        this.id = 0;
        this.arrived = new HashMap<>();
    }

    public CFGFuncNode(String funcName, List<String> parameters, int id) {
        this.funcName = funcName;
        this.parameters = parameters;
        this.root = null;
        this.id = id;
        this.arrived = new HashMap<>();
    }

    // Getters
    public String getFuncName() {
        return funcName;
    }


    public int getID() {
        return id;
    }

    public int getIDandADD(){
        id++;
        return id;
    }

    public List<String> getParameters() {
        return parameters;
    }

    public CFGStmtNode getRoot() {
        return root;
    }

    public Map<CFGStmtNode, Boolean> getArrived() {
        return arrived;
    }

    // Setters
    public void setFuncName(String funcName) {
        this.funcName = funcName;
    }

    public void setParameters(List<String> parameters) {
        this.parameters = parameters;
    }

    public void setArrived(CFGStmtNode stmt, boolean flag){
        this.arrived.put(stmt, flag);
    }

    // 添加参数
    public void addParameter(String parameter) {
        parameters.add(parameter);
    }

    public List<CFGStmtNode> getAllStmt(CFGStmtNode stmt){
        List<CFGStmtNode> result = new ArrayList<>();
        result.add(stmt);
        for (CFGStmtNode child : stmt.getChildren()){
            result.addAll(getAllStmt(child));
        }
        return result;
    }

    public void setRoot(CFGStmtNode root) {
        this.root = root;
    }

    public void setArrived(CFGStmtNode root){
        for (CFGStmtNode stmt : getAllStmt(root)){
            this.arrived.put(stmt, false);
        }
    }

    // 单函数打印
    public void printSingleFunc() {
        System.out.println("Function: " + funcName);
        System.out.println("Parameters: " + parameters);
        System.out.println("Root: \n" + root.printTree());
    }

    public Set<CFGStmtNode> getAllparents(CFGStmtNode stmt) {
        List<CFGStmtNode> list = new ArrayList<>();
        Set<CFGStmtNode> result = new HashSet<>();
        list.add(root);
        while (!list.isEmpty()) {
            CFGStmtNode node = list.remove(0);
            if (node.getChildren().contains(stmt)) {
                result.add(node);
            }
            list.addAll(node.getChildren());
        }
        return result;
    }
}
