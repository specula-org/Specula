import java.io.*;

import tla2sany.drivers.SANY;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.modanalyzer.ParseUnit;
import tla2sany.st.TreeNode;
import tla2sany.parser.SyntaxTreeNode;

import CFG.SANYCFGBuilder;
import CFG.CFGFuncNode;
import CFG.CFGStmtNode;

/**
 * Test robust junction handling with complex nested structures
 */
public class RobustJunctionTestRunner {
    
    public static void main(String[] args) {
        try {
            System.out.println("=== Testing Robust Junction Handling ===");
            
            // Parse with SANY
            SpecObj spec = new SpecObj("RobustJunctionTest.tla", null);
            int result = SANY.frontEndMain(spec, "RobustJunctionTest", System.out);
            
            if (result != 0) {
                System.err.println("SANY parsing failed");
                return;
            }
            
            // Get the AST
            String moduleName = "RobustJunctionTest";
            ParseUnit parseUnit = (ParseUnit) spec.parseUnitContext.get(moduleName);
            
            if (parseUnit == null) {
                System.err.println("No parse unit found");
                return;
            }
            
            TreeNode parseTree = parseUnit.getParseTree();
            if (parseTree == null) {
                System.err.println("No parse tree found");
                return;
            }
            
            // Build CFG using SANY
            System.out.println("\\n=== Building CFG from SANY AST ===");
            SANYCFGBuilder cfgBuilder = new SANYCFGBuilder();
            cfgBuilder.buildCFG(parseTree);
            
            // Display results
            System.out.println("\\n=== CFG Build Results ===");
            
            System.out.println("Variables: " + cfgBuilder.getVariables());
            System.out.println("Constants: " + cfgBuilder.getConstants());
            
            System.out.println("\\nFunctions:");
            for (CFGFuncNode funcNode : cfgBuilder.getCfgFuncNodes()) {
                System.out.println("\\n--- Function: " + funcNode.getFuncName() + " ---");
                System.out.println("Parameters: " + funcNode.getParameters());
                
                if (funcNode.getRoot() != null) {
                    System.out.println("CFG Structure:");
                    printCFGNode(funcNode.getRoot(), 0);
                    
                    System.out.println("\\nAnalysis:");
                    analyzeCFGStructure(funcNode.getFuncName(), funcNode.getRoot());
                }
            }
            
        } catch (Exception e) {
            System.err.println("Error: " + e.getMessage());
            e.printStackTrace();
        }
    }
    
    private static void printCFGNode(CFGStmtNode node, int depth) {
        if (node == null) return;
        
        String indent = "  ".repeat(depth);
        System.out.println(indent + "Node[" + node.getType() + "]: " + node.getContent());
        
        for (CFGStmtNode child : node.getChildren()) {
            printCFGNode(child, depth + 1);
        }
    }
    
    private static void analyzeCFGStructure(String funcName, CFGStmtNode root) {
        int skipNodes = countNodesByType(root, CFGStmtNode.StmtType.SKIP);
        int normalNodes = countNodesByType(root, CFGStmtNode.StmtType.NORMAL);
        int maxDepth = calculateMaxDepth(root);
        int maxBranches = calculateMaxBranches(root);
        
        System.out.println("  - SKIP nodes (disjunctions): " + skipNodes);
        System.out.println("  - NORMAL nodes (statements): " + normalNodes);
        System.out.println("  - Max depth: " + maxDepth);
        System.out.println("  - Max branches from single node: " + maxBranches);
        
        if (skipNodes > 0) {
            System.out.println("  - Contains parallel branches: YES");
        }
        if (maxDepth > 3) {
            System.out.println("  - Complex nesting detected: YES");
        }
    }
    
    private static int countNodesByType(CFGStmtNode node, CFGStmtNode.StmtType type) {
        if (node == null) return 0;
        
        int count = (node.getType() == type) ? 1 : 0;
        for (CFGStmtNode child : node.getChildren()) {
            count += countNodesByType(child, type);
        }
        return count;
    }
    
    private static int calculateMaxDepth(CFGStmtNode node) {
        if (node == null) return 0;
        
        int maxChildDepth = 0;
        for (CFGStmtNode child : node.getChildren()) {
            maxChildDepth = Math.max(maxChildDepth, calculateMaxDepth(child));
        }
        return 1 + maxChildDepth;
    }
    
    private static int calculateMaxBranches(CFGStmtNode node) {
        if (node == null) return 0;
        
        int maxBranches = node.getChildren().size();
        for (CFGStmtNode child : node.getChildren()) {
            maxBranches = Math.max(maxBranches, calculateMaxBranches(child));
        }
        return maxBranches;
    }
}