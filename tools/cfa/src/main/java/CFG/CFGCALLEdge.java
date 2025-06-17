package CFG;

public class CFGCALLEdge {
    private CFGStmtNode source;  // 调用点
    private CFGFuncNode sourceFunc;  // 调用点所在的函数
    private CFGFuncNode target;  // 被调用的函数
    private String[] arguments;  // 调用参数
    private String returnTarget; // 返回值赋值目标

    public CFGCALLEdge(CFGStmtNode source, CFGFuncNode sourceFunc, CFGFuncNode target, String[] arguments, String returnTarget) {
        this.source = source;
        this.sourceFunc = sourceFunc;
        this.target = target;
        this.arguments = arguments;
        this.returnTarget = returnTarget;
    }

    public CFGStmtNode getSource() {
        return source;
    }

    public CFGFuncNode getSourceFunc() {
        return sourceFunc;
    }

    public CFGFuncNode getTarget() {
        return target;
    }

    public String[] getArguments() {
        return arguments;
    }

    public String getReturnTarget() {
        return returnTarget;
    }

    public void setSource(CFGStmtNode source) {
        this.source = source;
    }

    public void setSourceFunc(CFGFuncNode sourceFunc) {
        this.sourceFunc = sourceFunc;
    }

    public void setTarget(CFGFuncNode target) {
        this.target = target;
    }

    public void setArguments(String[] arguments) {
        this.arguments = arguments;
    }

    public void setReturnTarget(String returnTarget) {
        this.returnTarget = returnTarget;
    }
}
