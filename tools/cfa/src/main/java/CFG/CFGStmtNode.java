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

    // Public copyTree method, initialize copy process
    public CFGStmtNode copyTree(CFGCALLGraph cfg, CFGFuncNode newfuncNode) {
        // Use a Map to track copied nodes, key is original node, value is corresponding copy node
        Map<CFGStmtNode, CFGStmtNode> copiedNodes = new HashMap<>();
        return copyTreeRecursive(copiedNodes, cfg, newfuncNode);
    }

    // Private recursive helper method
    private CFGStmtNode copyTreeRecursive(Map<CFGStmtNode, CFGStmtNode> copiedNodes, CFGCALLGraph cfg, CFGFuncNode newfuncNode) {
        // 1. Check if this node has been copied
        if (copiedNodes.containsKey(this)) {
            // If so, return the existing copy to maintain shared structure
            return copiedNodes.get(this);
        }

        // 2. If not copied, create new node
        CFGStmtNode newNode = new CFGStmtNode(this.getIndentation(), this.getContent(), this.getCtx(), this.getType());
        
        // 3. Put the newly created copy into the map, so that subsequent references can find it
        // This step must be completed before recursively copying child nodes, to correctly handle possible loops (although tree structures usually do not) and shared
        copiedNodes.put(this, newNode);

        // 4. Copy specific type attributes
        if (this.getType() == StmtType.LET) {
            // Assume getTemporaryVariables() returns Set<String>
            // Create a new Set instance, rather than sharing the reference of the original Set
            newNode.setTemporaryVariables(this.getTemporaryVariables());
        }
        // You may also need to copy other non-child node attributes here, ensure they are appropriately deep copied or shallow copied
        // Construct call edge
        if (this.getType() == StmtType.CALL) {
            List<CFGCALLEdge> edges = cfg.getCallEdgesFromStmt(this);
            for (CFGCALLEdge edge: edges){
                CFGCALLEdge newedge = new CFGCALLEdge(newNode, newfuncNode, edge.getTarget(), edge.getArguments(), edge.getReturnTarget());
                cfg.addCallEdge(newedge);
            }
        }

        // 5. Recursively copy child nodes
        for (CFGStmtNode child : this.getChildren()) {
            // Call recursive copy method for each child node
            // This ensures that if child nodes are shared, we get shared copies
            newNode.addChild(child.copyTreeRecursive(copiedNodes, cfg, newfuncNode));
        }
        
        return newNode;
    }
}