package CFG;

public class CFGCALLEdge {
    private CFGStmtNode source;  // Call point
    private CFGFuncNode sourceFunc;  // Function containing call point
    private CFGFuncNode target;  // Called function
    private String[] arguments;  // Call arguments
    private String returnTarget; // Return value assignment target

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
