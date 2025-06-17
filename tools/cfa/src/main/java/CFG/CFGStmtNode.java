package CFG;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.antlr.v4.runtime.ParserRuleContext; // For optional printTree enhancement

public class CFGStmtNode {
    private int indentation;
    private String content;
    private ParserRuleContext ctx;
    public Set<String> InVar;
    public Set<String> OutVar;
    private List<CFGStmtNode> children;
    private StmtType type;

    // New field for LET statements
    private List<String> temporaryVariables; // Stores names of variables declared in a LET statement

    public enum StmtType {
        NORMAL,
        IF_ELSE,
        CALL,
        ROOT,
        SKIP,
        LET
    }

    public CFGStmtNode(int indentation, String content, ParserRuleContext ctx, StmtType type) {
        this.indentation = indentation;
        this.content = content;
        this.ctx = ctx;
        this.type = type;
        this.InVar = new HashSet<>();
        this.OutVar = new HashSet<>();
        this.children = new ArrayList<>();
        // Initialize temporaryVariables as an empty list for all node types.
        // It will only be populated for LET nodes.
        this.temporaryVariables = new ArrayList<>();
    }

    // Getters
    public int getIndentation() {
        return indentation;
    }

    public String getContent() {
        return content;
    }

    public ParserRuleContext getCtx() {
        return ctx;
    }

    public StmtType getType() {
        return type;
    }

    // Getter for temporary variables
    // Returns an unmodifiable view to prevent external modification without using dedicated methods.
    public List<String> getTemporaryVariables() {
        if (this.type != StmtType.LET && !this.temporaryVariables.isEmpty()) {
            // This case should ideally not happen if logic is correct,
            // but good for a warning during development.
            System.err.println("Warning: Accessing temporary variables for a non-LET node that unexpectedly has them.");
        }
        return Collections.unmodifiableList(temporaryVariables);
    }

    // Setters
    public void setIndentation(int indentation) {
        this.indentation = indentation;
    }

    public void setContent(String content) {
        this.content = content;
    }

    public void setCtx(ParserRuleContext ctx) {
        this.ctx = ctx;
    }

    public void setType(StmtType type) {
        // If the type changes away from LET, we might want to clear temporary variables.
        if (this.type == StmtType.LET && type != StmtType.LET) {
            this.temporaryVariables.clear();
        }
        this.type = type;
    }

    // Method to add a single temporary variable, specific to LET nodes
    public void addTemporaryVariable(String varName) {
        if (this.type != StmtType.LET) {
            throw new IllegalStateException("Cannot add temporary variables to a node of type: " + this.type);
        }
        if (varName == null || varName.trim().isEmpty()) {
            throw new IllegalArgumentException("Temporary variable name cannot be null or empty.");
        }
        this.temporaryVariables.add(varName);
    }

    // Method to set all temporary variables at once, specific to LET nodes
    public void setTemporaryVariables(List<String> vars) {
        if (this.type != StmtType.LET) {
            throw new IllegalStateException("Cannot set temporary variables for a node of type: " + this.type);
        }
        if (vars == null) {
            throw new IllegalArgumentException("Temporary variables list cannot be null.");
        }
        this.temporaryVariables = new ArrayList<>(vars); // Create a defensive copy
    }


    public CFGStmtNode addChild(CFGStmtNode child) {
        if (child == null) {
            throw new RuntimeException("child is null");
        }
        children.add(child);
        return this;
    }

    public CFGStmtNode deleteChild(CFGStmtNode child) {
        children.remove(child);
        return this;
    }

    public CFGStmtNode deleteAllChild() {
        children.clear();
        return this;
    }

    public List<CFGStmtNode> getChildren() {
        return children; // Consider returning Collections.unmodifiableList(children) for stricter encapsulation
    }

    public String printTree() {
        StringBuilder sb = new StringBuilder();
        printTreeHelper(this, "", true, sb);
        return sb.toString();
    }

    private void printTreeHelper(CFGStmtNode node, String prefix, boolean isLast, StringBuilder sb) {
        sb.append(prefix);
        sb.append(isLast ? "└── " : "├── ");
        sb.append(node.content);

        // Optional: Display temporary variables for LET nodes
        if (node.getType() == StmtType.LET && !node.temporaryVariables.isEmpty()) {
            sb.append(" [DECLARES: ");
            sb.append(String.join(", ", node.temporaryVariables));
            sb.append("]");
        }
        // Optional: Display InVar/OutVar for debugging
        // if (!node.InVar.isEmpty()) sb.append(" In:").append(node.InVar);
        // if (!node.OutVar.isEmpty()) sb.append(" Out:").append(node.OutVar);

        sb.append("\n");

        for (int i = 0; i < node.children.size(); i++) {
            String newPrefix = prefix + (isLast ? "    " : "│   ");
            printTreeHelper(node.children.get(i), newPrefix, i == node.children.size() - 1, sb);
        }
    }

    // 公共的 copyTree 方法，初始化复制过程
    public CFGStmtNode copyTree(CFGCALLGraph cfg, CFGFuncNode newfuncNode) {
        // 使用一个 Map 来跟踪已复制的节点，键是原始节点，值是对应的副本节点
        Map<CFGStmtNode, CFGStmtNode> copiedNodes = new HashMap<>();
        return copyTreeRecursive(copiedNodes, cfg, newfuncNode);
    }

    // 私有的递归辅助方法
    private CFGStmtNode copyTreeRecursive(Map<CFGStmtNode, CFGStmtNode> copiedNodes, CFGCALLGraph cfg, CFGFuncNode newfuncNode) {
        // 1. 检查此节点是否已经被复制过
        if (copiedNodes.containsKey(this)) {
            // 如果是，则直接返回已存在的副本，以维护共享结构
            return copiedNodes.get(this);
        }

        // 2. 如果尚未复制，则创建新节点
        CFGStmtNode newNode = new CFGStmtNode(this.getIndentation(), this.getContent(), this.getCtx(), this.getType());
        
        // 3. 将新创建的副本放入映射中，以便后续引用可以找到它
        // 这一步必须在递归复制子节点之前完成，以正确处理可能的循环（尽管树结构通常没有）和共享
        copiedNodes.put(this, newNode);

        // 4. 复制特定类型的属性
        if (this.getType() == StmtType.LET) {
            // 假设 getTemporaryVariables() 返回 Set<String>
            // 创建一个新的 Set 实例，而不是共享原始 Set 的引用
            newNode.setTemporaryVariables(this.getTemporaryVariables());
        }
        // 您可能还需要在这里复制其他非子节点的属性，确保它们也被适当地深拷贝或浅拷贝
        // 构造调用边
        if (this.getType() == StmtType.CALL) {
            List<CFGCALLEdge> edges = cfg.getCallEdgesFromStmt(this);
            for (CFGCALLEdge edge: edges){
                CFGCALLEdge newedge = new CFGCALLEdge(newNode, newfuncNode, edge.getTarget(), edge.getArguments(), edge.getReturnTarget());
                cfg.addCallEdge(newedge);
            }
        }

        // 5. 递归复制子节点
        for (CFGStmtNode child : this.getChildren()) {
            // 对每个子节点调用递归复制方法
            // 这将确保如果子节点是共享的，我们会得到共享的副本
            newNode.addChild(child.copyTreeRecursive(copiedNodes, cfg, newfuncNode));
        }
        
        return newNode;
    }
}