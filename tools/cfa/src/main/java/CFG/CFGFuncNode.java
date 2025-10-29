package CFG;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class CFGFuncNode {
    private String funcName;  // Function name
    private List<String> parameters;  // Function parameter list
    private CFGStmtNode root;  // Function body statement node list 
    private int id;
    private Map<CFGStmtNode, Boolean> arrived;
    private boolean aliasOnly;  // Whether this function is only for alias definition
    private boolean pureExpression;
    private String originalExpression;
    public enum InvocationKind {
        ENTRY,
        CALLED
    }
    private InvocationKind invocationKind;

    // Constructor
    public CFGFuncNode(String funcName, List<String> parameters) {
        this.funcName = funcName;
        this.parameters = parameters;
        this.root = null;
        this.id = 0;
        this.arrived = new HashMap<>();
        this.aliasOnly = false;
        this.invocationKind = InvocationKind.ENTRY;
        this.pureExpression = false;
        this.originalExpression = null;
    }

    public CFGFuncNode(String funcName, List<String> parameters, int id) {
        this.funcName = funcName;
        this.parameters = parameters;
        this.root = null;
        this.id = id;
        this.arrived = new HashMap<>();
        this.aliasOnly = false;
        this.invocationKind = InvocationKind.ENTRY;
        this.pureExpression = false;
        this.originalExpression = null;
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

    public boolean isAliasOnly() {
        return aliasOnly;
    }

    public InvocationKind getInvocationKind() {
        return invocationKind;
    }

    public boolean isPureExpression() {
        return pureExpression;
    }

    public String getOriginalExpression() {
        return originalExpression;
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

    public void setAliasOnly(boolean aliasOnly) {
        this.aliasOnly = aliasOnly;
    }

    public void setInvocationKind(InvocationKind invocationKind) {
        this.invocationKind = invocationKind;
    }

    public boolean isEntryPoint() {
        return invocationKind == InvocationKind.ENTRY;
    }

    public void setPureExpression(boolean pureExpression) {
        this.pureExpression = pureExpression;
    }

    public void setOriginalExpression(String originalExpression) {
        this.originalExpression = originalExpression;
    }

    // Add parameter
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

    // Print single function
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
