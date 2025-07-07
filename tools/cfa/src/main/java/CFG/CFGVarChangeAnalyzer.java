package CFG;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Pattern;

public class CFGVarChangeAnalyzer {
    CFGCALLGraph callGraph;
    Set<String> variables;
    Map<String, Set<String>> funcVarChange;
    Map<CFGStmtNode, List<CFGStmtNode>> parentMap;
    List<CFGFuncNode> WorkList;
    Set<CFGFuncNode> cuttedFunc;
    Set<CFGFuncNode> rootFunc;
    Set<String> tempVars;
    public CFGVarChangeAnalyzer(CFGCALLGraph callGraph) {
        this.callGraph = callGraph;
        this.funcVarChange = new HashMap<>();
        this.variables = new HashSet<>();
        this.parentMap = new HashMap<>();
        this.WorkList = new ArrayList<>();
        this.cuttedFunc = new HashSet<>();
        this.tempVars = new HashSet<>();
        for (String funcName : callGraph.getFuncNames()) {
            this.funcVarChange.put(funcName, new HashSet<>());
        }
        for (String variable : callGraph.getVariables()) {
            this.variables.add(variable);
        }
    }
    public CFGVarChangeAnalyzer(CFGCALLGraph callGraph, Set<String> variables) {
        this.callGraph = callGraph;
        this.variables = variables;
        this.parentMap = new HashMap<>();
        for (String funcName : callGraph.getFuncNames()) {
            this.funcVarChange.put(funcName, new HashSet<>());
        }
        this.WorkList = new ArrayList<>();
        this.cuttedFunc = new HashSet<>();
        this.tempVars = new HashSet<>();
        this.funcVarChange = new HashMap<>();
        for (String funcName : callGraph.getFuncNames()) {
            this.funcVarChange.put(funcName, new HashSet<>());
        }
    }

    public CFGCALLGraph getCallGraph() {
        return callGraph;
    }

    public void analyze() {
        // System.err.println("begin analyze");
        clearUNCHANGED();
        // Get topological sequence
        List<CFGFuncNode> topologicalSort = callGraph.getTopologicalSort();
        // Reverse
        Collections.reverse(topologicalSort);
        for (CFGFuncNode funcNode : topologicalSort) {
            // Analyze each function
            analyzeFuncSA(funcNode);
        }
        //traverseTree();
        // Calculate functions that are not called in CallGraph
        Set<String> uncalledFunc = getUncalledFunc();
        rootFunc = new HashSet<>(callGraph.getFuncNodes());

        for (CFGFuncNode funcNode : topologicalSort){
            checkCuttedFunc(funcNode);
        }

        List<CFGFuncNode> funcNodes = new ArrayList<>(callGraph.getFuncNodes());
        WorkList.addAll(funcNodes);
        while (!WorkList.isEmpty()){
            tempVars = new HashSet<>();
            CFGFuncNode funcNode = WorkList.remove(0);
            if (uncalledFunc.contains(funcNode.getFuncName())){
                analyzeFuncPCUncalled(funcNode);
            } else {
                analyzeFuncPCCalled(funcNode);
            }
        }

        // Update funcVarChange
        updateFuncVarChange();
        List<CFGFuncNode> funclist = new ArrayList<>(callGraph.getFuncNodes());
        // Generate handle function
        for (CFGFuncNode funcNode : funclist){
            if (uncalledFunc.contains(funcNode.getFuncName())){
                genHandleUncalledFunc(funcNode);
            } else {
                genHandleCalledFunc(funcNode);
            }
        }
        
        analyzeUC();
        anlayzeUD();
    }

    public void analyze_only_sa(){
        List<CFGFuncNode> topologicalSort = callGraph.getTopologicalSort();
        // Reverse
        Collections.reverse(topologicalSort);
        for (CFGFuncNode funcNode : topologicalSort) {
            analyzeFuncSA(funcNode);
        }
    }

    public void analyze_only_pc(){
        // Get topological sequence
        List<CFGFuncNode> topologicalSort = callGraph.getTopologicalSort();
        // Reverse
        Collections.reverse(topologicalSort);
        for (CFGFuncNode funcNode : topologicalSort) {
            // Analyze each function
            analyzeFuncSA(funcNode);
        }
        //traverseTree();
        // Calculate functions that are not called in CallGraph
        Set<String> uncalledFunc = getUncalledFunc();
        rootFunc = new HashSet<>(callGraph.getFuncNodes());

        for (CFGFuncNode funcNode : topologicalSort){
            checkCuttedFunc(funcNode);
        }

        List<CFGFuncNode> funcNodes = new ArrayList<>(callGraph.getFuncNodes());
        WorkList.addAll(funcNodes);
        while (!WorkList.isEmpty()){
            tempVars = new HashSet<>();
            CFGFuncNode funcNode = WorkList.remove(0);
            if (uncalledFunc.contains(funcNode.getFuncName())){
                analyzeFuncPCUncalled(funcNode);
            } else {
                analyzeFuncPCCalled(funcNode);
            }
        }

        // Update funcVarChange
        updateFuncVarChange();
        List<CFGFuncNode> funclist = new ArrayList<>(callGraph.getFuncNodes());
        // Generate handle function
        for (CFGFuncNode funcNode : funclist){
            if (uncalledFunc.contains(funcNode.getFuncName())){
                genHandleUncalledFunc(funcNode);
            } else {
                genHandleCalledFunc(funcNode);
            }
        }
    }

    public void analyze_only_ud(){
        clearUNCHANGED();
        // Get topological sequence
        List<CFGFuncNode> topologicalSort = callGraph.getTopologicalSort();
        // Reverse
        Collections.reverse(topologicalSort);
        for (CFGFuncNode funcNode : topologicalSort) {
            // Analyze each function
            analyzeFuncSA(funcNode);
        }
        anlayzeUD();
    }

    public void analyze_only_uc(){
        clearUNCHANGED();
        List<CFGFuncNode> topologicalSort = callGraph.getTopologicalSort();
        // Reverse
        Collections.reverse(topologicalSort);
        for (CFGFuncNode funcNode : topologicalSort) {
            // Analyze each function
            analyzeFuncSA(funcNode);
        }
        analyzeUC();
    }

    // Static analysis build parent node mapping relationship and IN and OUT
    private void analyzeFuncSA(CFGFuncNode funcNode){
        CFGStmtNode stmtNode = funcNode.getRoot();
        buildParentMap(stmtNode);
        for (CFGStmtNode stmt : stmtNode.getChildren()) {
            analyzeStmtSA(funcNode, stmt, stmtNode.OutVar);
        }
        // Before handling control flow convergence point, build parent relationship
        funcVarChange.put(funcNode.getFuncName(), getAllLeafVar(stmtNode));
    }


    private void analyzeStmtSA(CFGFuncNode funcNode, CFGStmtNode stmt, Set<String> OutVar){
        // Static analysis
        // Traverse called functions, record changed variables, detect conflicts
        Set<String> INVar = stmt.InVar;
        INVar.addAll(OutVar);
        Set<String> VarDecl = new HashSet<>();
        List<CFGFuncNode> targetFunc = callGraph.getTargetFunc(stmt);
        for (CFGFuncNode targetFuncNode : targetFunc){
            Set<String> VarChanged = funcVarChange.get(targetFuncNode.getFuncName());
            for (String var : VarChanged){
                if (VarDecl.contains(var)){
                    // System.err.println("var: " + var);
                    // System.err.println("VarChanged: " + VarChanged);
                    throw new RuntimeException("Multi-function call variable modification conflict: " + VarDecl + " " + targetFuncNode.getFuncName() +  "  " + stmt.getContent() + "  " + funcNode.getFuncName());
                }
            }
            VarDecl.addAll(VarChanged);
        }
        // Variables changed by Stmt, detect conflicts
        Set<String> VarChangedStmt = VarChangedOneStmt(stmt);
        Set<String> intersection = new HashSet<>(VarChangedStmt);
        intersection.retainAll(VarDecl);
        if (!intersection.isEmpty()){
            // Print VarChangedStmt and VarDecl when error
            // System.err.println("VarChangedStmt: " + VarChangedStmt);
            // System.err.println("VarDecl: " + VarDecl);
            throw new RuntimeException("Multi-function call variable modification conflict: " + intersection + " "+ stmt.getContent());
        }
        Set<String> OUTVar = new HashSet<>();
        OUTVar.addAll(VarChangedStmt);
        OUTVar.addAll(VarDecl);
        OUTVar.addAll(INVar);
        stmt.OutVar = OUTVar;
        for (CFGStmtNode child : stmt.getChildren()){
            analyzeStmtSA(funcNode, child, OUTVar);
        }
    }

    private void analyzeFuncPCCalled(CFGFuncNode funcNode){
        CFGStmtNode stmtNode = funcNode.getRoot();
        // funcNode.setArrived(stmtNode);
        List<CFGStmtNode> stmtNodes = new ArrayList<>(stmtNode.getChildren());
        for (CFGStmtNode stmt : stmtNodes){
            analyzeStmtPC(funcNode, stmt);
        }
    }

    private void analyzeFuncPCUncalled(CFGFuncNode funcNode){
        CFGStmtNode stmtNode = funcNode.getRoot();
        // funcNode.setArrived(stmtNode);
        List<CFGStmtNode> stmtNodes = new ArrayList<>(stmtNode.getChildren());
        for (CFGStmtNode stmt : stmtNodes){
            analyzeStmtPC(funcNode, stmt);
        }
    }

    private void genHandleUncalledFunc(CFGFuncNode funcNode){
        // uncalled must be root
        // HandleFunc(args) == 
        //      /\ pc = Nil
        //      /\ func(args)
        //      /\ UNCHANGED <<vars - Vars_func>>
        //      /\ stack' = <<[backsite |-> Nil, info |-> [args |-> <<>>, temp |-> <<>>], args |-> <<>>]>>
        CFGFuncNode newFuncNode = new CFGFuncNode("Handle" + funcNode.getFuncName(), funcNode.getParameters(),0);            
        CFGStmtNode root = new CFGStmtNode(0, "root", null, CFGStmtNode.StmtType.ROOT);
        newFuncNode.setRoot(root);
        CFGStmtNode pc_stmt = new CFGStmtNode(1, "/\\ pc = Nil", null, CFGStmtNode.StmtType.NORMAL);
        root.addChild(pc_stmt);
        CFGStmtNode call_stmt = new CFGStmtNode(1, "/\\ " + Call_uncalled(funcNode), null, CFGStmtNode.StmtType.NORMAL);
        pc_stmt.addChild(call_stmt); 
        Set<String> unchangedVar = new HashSet<>(variables);
        unchangedVar.removeAll(funcVarChange.get(funcNode.getFuncName()));
        CFGStmtNode unchanged_stmt = new CFGStmtNode(1, getUnchangedVar(unchangedVar), null, CFGStmtNode.StmtType.NORMAL);
        call_stmt.addChild(unchanged_stmt);
        callGraph.addFuncNode(newFuncNode);
        CFGCALLEdge callEdge = new CFGCALLEdge(call_stmt, newFuncNode, funcNode, null, null);
        callGraph.addCallEdge(callEdge);
        CFGStmtNode stack_stmt = new CFGStmtNode(1, "/\\ stack' = <<[backsite |-> Nil, info |-> [args |-> <<>>, temp |-> <<>>], args |-> <<>>]>>", null, CFGStmtNode.StmtType.NORMAL);
        call_stmt.addChild(stack_stmt);
    }

    private void genHandleCalledFunc(CFGFuncNode funcNode){
        // Func not cut: return directly
        // Func cut:
        // HandleFunc(args) == 
        //      /\ pc = funcname
        //      /\ func(stack.args)
        //      /\ UNCHANGED <<vars - Vars_func>>
        if (cuttedFunc.contains(funcNode)){
            // Cut
            CFGFuncNode newFuncNode = new CFGFuncNode("Handle" + funcNode.getFuncName(), new ArrayList<>(),0);            
            CFGStmtNode root = new CFGStmtNode(0, "root", null, CFGStmtNode.StmtType.ROOT);
            newFuncNode.setRoot(root);
            CFGStmtNode pc_stmt = new CFGStmtNode(1, "/\\ pc = \"" + funcNode.getFuncName() + "\"", null, CFGStmtNode.StmtType.NORMAL);
            root.addChild(pc_stmt);
            CFGStmtNode call_stmt;
            if (rootFunc.contains(funcNode)){
                call_stmt = new CFGStmtNode(1, "/\\ " + Call_root_called(funcNode), null, CFGStmtNode.StmtType.NORMAL);
            } else {
                call_stmt = new CFGStmtNode(1, "/\\ " + Call_nonroot_called(funcNode), null, CFGStmtNode.StmtType.NORMAL);
            }
            pc_stmt.addChild(call_stmt);
            Set<String> unchangedVar = new HashSet<>(variables);
            unchangedVar.removeAll(funcVarChange.get(funcNode.getFuncName()));
            CFGStmtNode unchanged_stmt = new CFGStmtNode(1, getUnchangedVar(unchangedVar), null, CFGStmtNode.StmtType.NORMAL);
            call_stmt.addChild(unchanged_stmt);
            callGraph.addFuncNode(newFuncNode);
            CFGCALLEdge callEdge = new CFGCALLEdge(call_stmt, newFuncNode, funcNode, null, null);
            callGraph.addCallEdge(callEdge);
        }
    }

    private void analyzeStmtPC(CFGFuncNode funcNode, CFGStmtNode stmt){
        Set<String> tempVarsThisFunc = new HashSet<>(tempVars);
        // System.err.println("tempVarsThisFunc: " + tempVarsThisFunc);
        // System.err.println("stmt: " + stmt.getContent());
        if (stmt.getType() == CFGStmtNode.StmtType.LET){
            tempVarsThisFunc.addAll(stmt.getTemporaryVariables());
        }
        boolean flag = false;
        Set<String> intersection = new HashSet<>(stmt.InVar);
        Set<String> declVar = new HashSet<>();
        if (stmt.getType() == CFGStmtNode.StmtType.CALL){
            List<CFGFuncNode> targetFunc = callGraph.getTargetFunc(stmt);
            for (CFGFuncNode targetFuncNode : targetFunc){
                declVar.addAll(funcVarChange.get(targetFuncNode.getFuncName()));
                if (cuttedFunc.contains(targetFuncNode)){
                    flag = true;
                }
            }
        }
        declVar.addAll(VarChangedOneStmt(stmt));
        intersection.retainAll(declVar);
        // Discuss by cases:
        if (flag) {
            // If already cut, need to cut this function
            int id = funcNode.getIDandADD();
            CFGFuncNode newFuncNode = new CFGFuncNode(funcNode.getFuncName() + "_" + id, funcNode.getParameters(), id);
            CFGStmtNode root = new CFGStmtNode(0, "root", null, CFGStmtNode.StmtType.ROOT);
            newFuncNode.setRoot(root);
            CFGStmtNode start_stmt = null;
            if (!stmt.getChildren().isEmpty()){
                // Use the children of stmt as the first node of the new function, and copy all subsequent nodes to form a new function
                start_stmt = stmt.getChildren().get(0).copyTree(callGraph, newFuncNode);
            } else {
                start_stmt = new CFGStmtNode(1, "/\\ UNCHANGED <<vars>> ", null, CFGStmtNode.StmtType.NORMAL);
            }
            root.addChild(start_stmt);

            Set<CFGStmtNode> parents = funcNode.getAllparents(stmt);
            List<CFGFuncNode> targetFunc = callGraph.getTargetFunc(stmt);
            CFGStmtNode pc_jump = null;
            if (targetFunc.size() == 1){
                pc_jump = new CFGStmtNode(stmt.getIndentation(), "/\\ pc' = \"" + targetFunc.get(0).getFuncName() + "\"", null, CFGStmtNode.StmtType.NORMAL);
            } else {
                // Error: temporarily not supported
                throw new RuntimeException("Multi-function call variable modification conflict: " + targetFunc);
            }
            // pc' = name
            // info' = [args |-> <<>>, temp |-> [temp1 |-> temp1, temp2 |-> temp2, ...]]
            // stack'= Append(stack, [backsite |-> newfuncname, args |-> <<>>, info |-> info'])
            pc_jump.InVar = new HashSet<>(stmt.InVar);
            pc_jump.OutVar = new HashSet<>(stmt.InVar);
            pc_jump.OutVar.add("pc");
            // Add pc_jump
            for (CFGStmtNode parent : parents){
                parent.deleteChild(stmt);
                parent.addChild(pc_jump);
                parentMap.computeIfAbsent(pc_jump, k -> new ArrayList<>()).add(parent);
            }
            updateNewFuncCallEdge(newFuncNode, root);
            // New InVar OutVar is cleared
            resetInOutVar(root);
            // Generated function also needs to be analyzed, added to subsequent Worklist
            analyzeFuncSA(newFuncNode);
            WorkList.add(newFuncNode);
            cuttedFunc.add(newFuncNode);
            callGraph.addFuncNode(newFuncNode);
            CFGStmtNode info_node = new CFGStmtNode(stmt.getIndentation(), setInfoStr(funcNode.getParameters(), tempVarsThisFunc), null, CFGStmtNode.StmtType.NORMAL);
            info_node.InVar = new HashSet<>(pc_jump.OutVar);
            info_node.OutVar = new HashSet<>(pc_jump.OutVar);
            info_node.OutVar.add("info");
            pc_jump.addChild(info_node);
            parentMap.computeIfAbsent(info_node, k -> new ArrayList<>()).add(pc_jump);
            CFGStmtNode stack_node = new CFGStmtNode(stmt.getIndentation(), updateStackStr(newFuncNode, stmt.getContent()), null, CFGStmtNode.StmtType.NORMAL);
            stack_node.InVar = new HashSet<>(info_node.OutVar);
            stack_node.OutVar = new HashSet<>(info_node.OutVar);
            stack_node.OutVar.add("stack");
            pc_jump.addChild(stack_node);
            parentMap.computeIfAbsent(stack_node, k -> new ArrayList<>()).add(info_node);
            // Change temporary variables in new function to variables in info
            updateNewFuncTempVars(newFuncNode, tempVarsThisFunc);
        } else {
            // If not cut, no conflict, no need to cut
            // If conflict, still need to cut
            if (intersection.isEmpty()){
                // No conflict, no need to cut
                List<CFGStmtNode> children = new ArrayList<>(stmt.getChildren());
                if (!children.isEmpty()){
                    for (CFGStmtNode child : children){
                        tempVars = new HashSet<>(tempVarsThisFunc);
                        analyzeStmtPC(funcNode, child);
                    }
                } else {
                    // No children, is return node, then need to pop stack
                    //     pc' = stack[Len(stack)].backsite
                    //     info' = stack[Len(stack)].info
                    //     stack' = Tail(stack)
                    Set<String> uncalledFunc = getUncalledFunc();
                    if ((cuttedFunc.contains(funcNode) && !uncalledFunc.contains(funcNode.getFuncName())) && !stmt.getContent().contains("/\\ info' =") && !stmt.getContent().contains("/\\ stack' =")){
                        CFGStmtNode pc_stmt = new CFGStmtNode(stmt.getIndentation(), "/\\ pc' = stack[Len(stack)].backsite", null, CFGStmtNode.StmtType.NORMAL);
                        pc_stmt.InVar = new HashSet<>(stmt.OutVar);
                        pc_stmt.OutVar = new HashSet<>(stmt.OutVar);
                        pc_stmt.OutVar.add("pc");
                        stmt.addChild(pc_stmt);
                        parentMap.computeIfAbsent(pc_stmt, k -> new ArrayList<>()).add(stmt);
                        CFGStmtNode stack_node = new CFGStmtNode(stmt.getIndentation(), "/\\ stack' = Tail(stack)", null, CFGStmtNode.StmtType.NORMAL);
                        stack_node.InVar = new HashSet<>(pc_stmt.OutVar);
                        stack_node.OutVar = new HashSet<>(pc_stmt.OutVar);
                        stack_node.OutVar.add("stack");
                        pc_stmt.addChild(stack_node);
                        parentMap.computeIfAbsent(stack_node, k -> new ArrayList<>()).add(pc_stmt);
                        CFGStmtNode info_node = new CFGStmtNode(stmt.getIndentation(), "/\\ info' = stack[Len(stack)].info", null, CFGStmtNode.StmtType.NORMAL);
                        info_node.InVar = new HashSet<>(stack_node.OutVar);
                        info_node.OutVar = new HashSet<>(stack_node.OutVar);
                        info_node.OutVar.add("info");
                        stack_node.addChild(info_node);
                        parentMap.computeIfAbsent(info_node, k -> new ArrayList<>()).add(stack_node);
                    }
                }
            } else {
                // Conflict, need to cut
                // Initialize the function cut out
                int id = funcNode.getIDandADD();
                CFGFuncNode newFuncNode = new CFGFuncNode(funcNode.getFuncName() + "_" + id, funcNode.getParameters(), id);
                CFGStmtNode root = new CFGStmtNode(0, "root", null, CFGStmtNode.StmtType.ROOT);
                newFuncNode.setRoot(root);
                // Cut
                Set<CFGStmtNode> parents = funcNode.getAllparents(stmt);
                CFGStmtNode pc_stmt_copy = stmt.copyTree(callGraph, newFuncNode);
                root.addChild(pc_stmt_copy);
                // Generate pc' = <<name, args>>
                String parameters = "[]";
                Boolean first = true;
                for (String parameter : funcNode.getParameters()){
                    if (first){
                        parameters += parameter;
                        first = false;
                    } else {
                        parameters += ", " + parameter;
                    }
                }
                CFGStmtNode pc_jump = new CFGStmtNode(stmt.getIndentation(), "/\\ pc' = \"" + funcNode.getFuncName() + "_" + id + "\"", null, CFGStmtNode.StmtType.NORMAL);
                // Check if the OutVar of all parents is the same, otherwise error
                // for (CFGStmtNode parent : parents){
                //     if (!parent.OutVar.equals(stmt.InVar)){
                //         throw new RuntimeException("Multi-function call variable modification conflict: " + parent.OutVar + " " + stmt.InVar);
                //     }
                // }
                pc_jump.InVar = new HashSet<>(stmt.InVar);
                pc_jump.OutVar = new HashSet<>(stmt.InVar);
                pc_jump.OutVar.add("pc");
                // Add pc_jump
                for (CFGStmtNode parent : parents){
                    parent.deleteChild(stmt);
                    parent.addChild(pc_jump);
                    parentMap.computeIfAbsent(pc_jump, k -> new ArrayList<>()).add(parent);
                }
                updateNewFuncCallEdge(newFuncNode, root);
                // New InVar OutVar is cleared
                resetInOutVar(root);
                // Generated function also needs to be analyzed, added to subsequent Worklist
                analyzeFuncSA(newFuncNode);
                WorkList.add(newFuncNode);
                cuttedFunc.add(newFuncNode);
                callGraph.addFuncNode(newFuncNode);
                CFGStmtNode info_node;
                if (rootFunc.contains(funcNode)){
                    info_node = new CFGStmtNode(stmt.getIndentation(), setInfoStr(funcNode.getParameters(), tempVarsThisFunc), null, CFGStmtNode.StmtType.NORMAL);
                } else {
                    info_node = new CFGStmtNode(stmt.getIndentation(), updateInfoStr(tempVarsThisFunc), null, CFGStmtNode.StmtType.NORMAL);
                }
                info_node.InVar = new HashSet<>(pc_jump.OutVar);
                info_node.OutVar = new HashSet<>(pc_jump.OutVar);
                info_node.OutVar.add("info");
                pc_jump.addChild(info_node);
                parentMap.computeIfAbsent(info_node, k -> new ArrayList<>()).add(pc_jump);
                // Change temporary variables in new function to variables in info
                updateNewFuncTempVars(newFuncNode, tempVarsThisFunc);
            }
        }
    }

    private void analyzeUC(){
        // Traverse all functions, analyze
        for (CFGFuncNode funcNode : callGraph.getFuncNodes()){
            analyzeFuncUC(funcNode);
        }
    }
 
    private void analyzeFuncUC(CFGFuncNode funcNode){
        // Traverse nodes with multiple parents
        CFGStmtNode stmtNode = funcNode.getRoot();
        Set<CFGStmtNode> stmtSet = new HashSet<>(parentMap.keySet());
        for (CFGStmtNode stmt : stmtSet) {
            if (parentMap.get(stmt).size() <= 1) {
                continue;
            }
            List<CFGStmtNode> parents = new ArrayList<>(parentMap.get(stmt));
            Iterator<CFGStmtNode> iterator = parents.iterator();
            while (iterator.hasNext()) {
                CFGStmtNode parent = iterator.next();
                // diff = stmt.InVar - parent.OutVar
                Set<String> diff = new HashSet<>(stmt.InVar);
                diff.removeAll(parent.OutVar);
                if (!diff.isEmpty()) {
                    // Create CFGStmtNode node
                    String unchangedVar = "/\\ UNCHANGED <<";
                    boolean first = true;
                    for (String var : diff) {
                        if (!first) {
                            unchangedVar += ", ";
                        }
                        unchangedVar += var;
                        first = false;
                    }
                    unchangedVar += ">>";
                    CFGStmtNode newStmt = new CFGStmtNode(parent.getIndentation(), unchangedVar, null, CFGStmtNode.StmtType.NORMAL);
                    newStmt.InVar = parent.OutVar;
                    newStmt.OutVar = stmt.InVar;
                    parent.deleteChild(stmt);
                    parent.addChild(newStmt);
                    newStmt.addChild(stmt);
                    // Update parentMap, remove parent of stmt, add newStmt
                    parentMap.computeIfAbsent(stmt, k -> new ArrayList<>()).remove(parent);
                    parentMap.computeIfAbsent(stmt, k -> new ArrayList<>()).add(newStmt);
                    parentMap.computeIfAbsent(newStmt, k -> new ArrayList<>()).add(parent);
                }
            }
        }
        // Handle control flow end
        Set<String> LeafVar = getAllLeafVar(stmtNode);
        // System.err.println("LeafVar: " + LeafVar);
        List<CFGStmtNode> LeafNode = getAllLeafNode(stmtNode);
        // for (CFGStmtNode leafNode : LeafNode) {
        //     System.err.println("LeafNode: " + leafNode.OutVar + " " + leafNode.getContent());
        // }
        for (CFGStmtNode leafNode : LeafNode) {
            Set<String> diff = new HashSet<>(LeafVar);
            diff.removeAll(leafNode.OutVar);
            if (!diff.isEmpty()) {
                // Create CFGStmtNode node
                String unchangedVar = "/\\ UNCHANGED <<";
                boolean first = true;
                for (String var : diff) {
                    if (!first) {
                        unchangedVar += ", ";
                    }
                    unchangedVar += var;
                    first = false;
                }
                unchangedVar += ">>";
                CFGStmtNode newStmt = new CFGStmtNode(leafNode.getIndentation(), unchangedVar, null, CFGStmtNode.StmtType.NORMAL);
                newStmt.InVar = leafNode.OutVar;
                newStmt.OutVar = LeafVar;
                leafNode.addChild(newStmt);
                parentMap.computeIfAbsent(newStmt, k -> new ArrayList<>()).add(leafNode);
            }
        }
    }   

    private void anlayzeUD(){
        for (CFGFuncNode funcNode : callGraph.getFuncNodes()){
            Map<CFGStmtNode, Boolean> stmtUD = new HashMap<>();
            analyzeFuncUD(funcNode, stmtUD);
        }
    }

    private void analyzeFuncUD(CFGFuncNode funcNode, Map<CFGStmtNode, Boolean> stmtUD){
        CFGStmtNode stmtNode = funcNode.getRoot();
        analyzeStmtUD(funcNode, stmtNode, stmtUD);
    }

    private void analyzeStmtUD(CFGFuncNode funcNode, CFGStmtNode stmtNode, Map<CFGStmtNode, Boolean> stmtUD){
        if (stmtUD.containsKey(stmtNode)) {
            return;
        }
        stmtUD.put(stmtNode, true);
        
        // Handle the content of the current node
        String content = stmtNode.getContent();
        for (String var : stmtNode.InVar) {
            Set<String> skip_set = new HashSet<String>(Arrays.asList("info", "pc", "stack"));
            if (skip_set.contains(var)) {
                continue;
            }
            // Build regular expression: variable cannot be letter, number, underscore, and cannot be followed by '
            String pattern = "(?<![\\w_])" + var + "(?!')(?![\\w_])";
            if (content.matches(".*" + pattern + ".*")) {
                // Replace variable, add ' after
                content = content.replaceAll(pattern, var + "'");
            }
        }
        stmtNode.setContent(content);
        
        // Recursively process children
        for (CFGStmtNode child : stmtNode.getChildren()) {
            analyzeStmtUD(funcNode, child, stmtUD);
        }
    }

    public Set<String> VarChangedOneStmt(CFGStmtNode stmt) {
        Set<String> result = new HashSet<>();
        String content = stmt.getContent();
        
        for (String var : variables) {
            // Updated regex pattern to match TLA+ variable assignment patterns
            // Matches: var' = ..., var' = [var EXCEPT ...], etc.
            String pattern = "(?<![\\w_])" + var + "'\\s*=";
            if (content.matches(".*" + pattern + ".*")) {
                result.add(var);
            }
        }
        
        // Handle UNCHANGED statement with alias support
        if (content.contains("UNCHANGED")) {
            // Extract variables from UNCHANGED << >>
            if (content.contains("<<")){
                int start = content.indexOf("<<");
                int end = content.indexOf(">>");
                if (start != -1 && end != -1) {
                    String vars = content.substring(start + 2, end);
                    String[] varArray = vars.split(",");
                    for (String var : varArray) {
                        String trimmedVar = var.trim();
                        // Check if it's a direct variable
                        if (variables.contains(trimmedVar)) {
                            result.add(trimmedVar);
                        }
                        // Check if it's an alias and resolve it
                        else if (callGraph.isAlias(trimmedVar)) {
                            List<String> resolvedVars = callGraph.resolveAlias(trimmedVar);
                            result.addAll(resolvedVars);
                        }
                    }
                }
            } else {
                // Handle UNCHANGED vars pattern (single variable or alias)
                String unchangedPattern = "UNCHANGED\\s+(\\w+)";
                java.util.regex.Pattern pattern = java.util.regex.Pattern.compile(unchangedPattern);
                java.util.regex.Matcher matcher = pattern.matcher(content);
                if (matcher.find()) {
                    String var = matcher.group(1);
                    // Check if it's a direct variable
                    if (variables.contains(var)) {
                        result.add(var);
                    }
                    // Check if it's an alias and resolve it
                    else if (callGraph.isAlias(var)) {
                        List<String> resolvedVars = callGraph.resolveAlias(var);
                        result.addAll(resolvedVars);
                    }
                }
            }
        }
        
        return result;
    }

    private Set<String> getAllLeafVar(CFGStmtNode stmt) {
        List<CFGStmtNode> LeafNode = getAllLeafNode(stmt);
        Set<String> result = new HashSet<>();
        for (CFGStmtNode leafNode : LeafNode) {
            result.addAll(leafNode.OutVar);
        }
        return result;
    }

    private List<CFGStmtNode> getAllLeafNode(CFGStmtNode stmt) {
        // Create a helper method, use Set to track visited nodes
        Set<CFGStmtNode> visited = new HashSet<>();
        List<CFGStmtNode> result = new ArrayList<>();
        getAllLeafNodeHelper(stmt, result, visited);
        return result;
    }

    private void getAllLeafNodeHelper(CFGStmtNode stmt, List<CFGStmtNode> result, Set<CFGStmtNode> visited) {
        // If already visited this node, return
        if (visited.contains(stmt)) {
            return;
        }
        
        // Mark as visited
        visited.add(stmt);
        
        if (!stmt.getChildren().isEmpty()) {
            // Non-leaf node, recursively process its children
            for (CFGStmtNode child : stmt.getChildren()) {
                getAllLeafNodeHelper(child, result, visited);
            }
        } else {
            // Leaf node, add to result list
            result.add(stmt);
        }
    }
    

    private void buildParentMap(CFGStmtNode root) {
        if (root == null || root.getChildren() == null) {
            return;
        }
        for (CFGStmtNode child : root.getChildren()) {
            //System.err.println("child: " + child.getContent() + child);
            addParentMap(child, root);
            buildParentMap(child);
        }
    }

    private void addParentMap(CFGStmtNode stmt, CFGStmtNode parent) {
        if (parentMap.containsKey(stmt)) {
            parentMap.get(stmt).add(parent);
        } else {
            parentMap.put(stmt, new ArrayList<>(Arrays.asList(parent)));
        }
    }

    private void traverseTree(){
        for (CFGFuncNode funcNode : callGraph.getFuncNodes()){
            CFGStmtNode stmtNode = funcNode.getRoot();
            traverseTreeHelper(stmtNode);
        }
    }

    private void traverseTreeHelper(CFGStmtNode stmtNode){
        // System.err.println("stmtNode: " + stmtNode.getContent());
        // System.err.println("IN: " + stmtNode.InVar);
        // System.err.println("OUT: " + stmtNode.OutVar);
        for (CFGStmtNode child : stmtNode.getChildren()){
            // Print IN and OUT
            traverseTreeHelper(child);
        }
    }

    private void updateNewFuncCallEdge(CFGFuncNode newFuncNode,CFGStmtNode stmt){
        if (stmt.getType() == CFGStmtNode.StmtType.CALL){
            // Traverse all function names for matching
            for (String funcName : callGraph.getFuncNames()) {
                // Build regular expression pattern - function name cannot be letter, number, underscore
                String pattern = "(?<![\\w_])" + funcName + "(?![\\w_])";
                // If find matching
                if (stmt.getContent().matches(".*" + pattern + ".*")) {
                    // Find corresponding target function node
                    CFGFuncNode targetFunc = null;
                    for (CFGFuncNode fn : callGraph.getFuncNodes()) {
                        if (fn.getFuncName().equals(funcName)) {
                            targetFunc = fn;
                            break;
                        }
                    }
                    if (targetFunc != null) {
                        // Check if this edge already exists
                        boolean edgeExists = false;
                        // Assume callGraph has a getCallEdges() method that returns Collection<CFGCALLEdge>
                        // And CFGCALLEdge has getSourceNode(), getCallerFunc(), getCalledFunc() method
                        if (callGraph.getCallEdges() != null) { // Defensive check
                            for (CFGCALLEdge existingEdge : callGraph.getCallEdges()) {
                                if (existingEdge.getSource() == stmt &&
                                    existingEdge.getSourceFunc() == newFuncNode &&
                                    existingEdge.getTarget() == targetFunc) {
                                    // If parameters and return values may also change and affect the uniqueness of the edge, also compare here
                                    edgeExists = true;
                                    break;
                                }
                            }
                        }

                        if (!edgeExists) {
                            // Create new call edge
                            CFGCALLEdge callEdge = new CFGCALLEdge(stmt, newFuncNode, targetFunc, new String[0], null);
                            callGraph.addCallEdge(callEdge);
                        }
                    }
                }
            }
        }
        for (CFGStmtNode child : stmt.getChildren()){
            updateNewFuncCallEdge(newFuncNode, child);
        }
    }

    public void resetInOutVar(CFGStmtNode node){
        node.InVar = new HashSet<>();
        node.OutVar = new HashSet<>();
        for (CFGStmtNode child : node.getChildren()){
            resetInOutVar(child);
        }
    }

    public void checkCuttedFunc(CFGFuncNode funcNode){
        for (CFGStmtNode stmt : funcNode.getRoot().getChildren()){
            checkCuttedFuncHelper(funcNode, stmt);
        }
    }

    public Set<String> getUncalledFunc() {
        Set<String> uncalledFunc = new HashSet<>(callGraph.getFuncNames());
        List<CFGCALLEdge> edges = callGraph.getCallEdges();
        for (CFGCALLEdge edge : edges){
            uncalledFunc.remove(edge.getTarget().getFuncName());
        }
        return uncalledFunc;
    }

    private String Call_root_called(CFGFuncNode funcNode){
        String callsite = funcNode.getFuncName();
        if (!funcNode.getParameters().isEmpty()){
            callsite += "(" + "stack.args[1]";
            for (int i = 1; i < funcNode.getParameters().size(); i++){
                callsite += ", " + "stack.args[" + (i + 1) + "]";
            }
            callsite += ")";
        }
        return callsite;
    }

    private String Call_nonroot_called(CFGFuncNode funcNode){
        String callsite = funcNode.getFuncName();
        if (!funcNode.getParameters().isEmpty()){
            callsite += "(" + "info.args[1]";
            for (int i = 1; i < funcNode.getParameters().size(); i++){
                callsite += ", " + "info.args[" + (i + 1) + "]";
            }
            callsite += ")";
        }
        return callsite;
    }

    private String Call_uncalled(CFGFuncNode funcNode){
        String callsite = funcNode.getFuncName();
        if (!funcNode.getParameters().isEmpty()){
            callsite += "(" + funcNode.getParameters().get(0);
            for (int i = 1; i < funcNode.getParameters().size(); i++){
                callsite += ", " + funcNode.getParameters().get(i);
            }
            callsite += ")";
        }
        return callsite;
    }

    private String getUnchangedVar(Set<String> vars){
        String unchangedVar = "/\\ UNCHANGED <<";
        boolean first = true;
        for (String var : vars) {
            if (!first) {
                unchangedVar += ", ";
            }
            unchangedVar += var;
            first = false;
        }
        unchangedVar += ">>";
        return unchangedVar;    
    }

    public void checkCuttedFuncHelper(CFGFuncNode funcNode, CFGStmtNode stmt){
        boolean flag = false;
        Set<String> intersection = new HashSet<>(stmt.InVar);
        Set<String> declVar = new HashSet<>();
        if (stmt.getType() == CFGStmtNode.StmtType.CALL){
            List<CFGFuncNode> targetFunc = callGraph.getTargetFunc(stmt);
            for (CFGFuncNode targetFuncNode : targetFunc){
                declVar.addAll(funcVarChange.get(targetFuncNode.getFuncName()));
                if (cuttedFunc.contains(targetFuncNode)){
                    flag = true;
                }
            }
        }
        declVar.addAll(VarChangedOneStmt(stmt));
        intersection.retainAll(declVar);
        // Discuss in different cases:
        if (flag) {
            // If already cut, need to cut this function
            cuttedFunc.add(funcNode);
        } else {
            // If not cut, no need to cut
            if (intersection.isEmpty()){
                // No conflict, no need to cut
                for (CFGStmtNode child : stmt.getChildren()){
                    checkCuttedFuncHelper(funcNode, child);
                }
            } else {
                // Conflict, need to cut
                cuttedFunc.add(funcNode);
            }
        }
    }

    private String setInfoStr(List<String> args, Set<String> temp){
        String infoStr = "/\\ info' = [";
        String argsStr = "<<";
        if (!args.isEmpty()){
            argsStr += args.get(0);
            for (int i = 1; i < args.size(); i++){
                argsStr += ", " + args.get(i);
            }
        }
        argsStr += ">>";
        infoStr += "args |-> " + argsStr + ", ";
        // tempStr = [temp1 |-> temp1, temp2 |-> temp2, ...]
        String tempStr;
        if (!temp.isEmpty()) {
            tempStr = "[";
            List<String> tempList = new ArrayList<>(temp);
            tempStr += tempList.get(0) + " |-> " + tempList.get(0);
            for (int i = 1; i < tempList.size(); i++) {
                tempStr += ", " + tempList.get(i) + " |-> " + tempList.get(i);
            }
            tempStr += "]";
        } else {
            tempStr = "<<>>";
        }
        infoStr += "temp |-> " + tempStr;
        infoStr += "]";
        return infoStr;
    }

    private String updateInfoStr(Set<String> temp){
        // If tempVars are a, b, c
        // info' = [temp |-> [a |-> a, b |-> b, c |-> c]] @@ info
        String infoStr = "/\\ info' = ";
        // tempStr = [temp |-> [a |-> a, b |-> b, c |-> c]] @@ info   OR    info
        String tempStr = "[temp |-> [";
        if (!temp.isEmpty()) {
            boolean first = true;
            for (String var: temp){
                if (first){
                    tempStr += var + " |-> " + var;
                    first = false;
                } else {
                    tempStr += ", " + var + " |-> " + var;
                }
            }
            tempStr += "]] @@ info";
        } else {
            tempStr = "info";
        }
        infoStr += tempStr;
        return infoStr;
    }

    private String updateStackStr(CFGFuncNode funcNode, String callsite){
        String arguments = "<< ";
        // callsite = "func(args)" Extract args and write as <<>>
        int start = callsite.indexOf("(");
        // Check if '(' is found
        if (start != -1) {
            // Find last ')'
            int end = callsite.lastIndexOf(")");
            // Ensure ')' is found and it is after '('
            if (end != -1 && end > start) {
                arguments += callsite.substring(start + 1, end);
            }
            // If no matching ')' or ')' is before '(', the parameter part is an empty string
        }
        // If no '(', the parameter part is an empty string
        arguments += ">>";
        String stackStr = "/\\ stack' = Append(stack, [backsite |-> \"" + funcNode.getFuncName() + "\", args |-> " + arguments + ", info |-> info'])";
        return stackStr;
    }

    private void updateNewFuncTempVars (CFGFuncNode newFuncNode, Set<String> temp)  {
        if (temp.isEmpty()){
            return;
        }
        // Check all CFGStmtNode in newFuncNode
        // If a statement uses a variable in tempVars, replace it with a variable in info, the matching rule is that var string is not letter, number, underscore, then it is considered a match
        // Example: uses a variable, replace with info.temp.a
        List<CFGStmtNode> StmtNodelist = new ArrayList<>(newFuncNode.getRoot().getChildren());
        while (!StmtNodelist.isEmpty()){
            CFGStmtNode stmt = StmtNodelist.remove(0);
            String content = stmt.getContent();
            for (String var : temp) {
                String pattern = "(?<!\\w)(?<!info\\.temp\\.)" + var + "(?!\\w)";       // NEW, using var directly

                // System.err.println("content: " + content);
                // System.err.println("var: " + var);
                // Add (?s) flag at the beginning of the regular expression, so that . (dot) can match any character including line breaks
                if (content.matches("(?s).*" + pattern + ".*")) { 
                    // System.err.println("tempVars1111: " + temp);
                    content = content.replaceAll(pattern, "info.temp." + var); 
                    stmt.setContent(content);
                }
            }
            StmtNodelist.addAll(stmt.getChildren());
        }
    }
    
    private void updateFuncVarChange(){
        for (CFGFuncNode funcNode : callGraph.getFuncNodes()){
            Set<String> varChange = new HashSet<>();
            List<CFGStmtNode> leafNodes = getAllLeafNode(funcNode.getRoot());
            for (CFGStmtNode leafNode : leafNodes){
                varChange.addAll(leafNode.OutVar);
            }
            funcVarChange.put(funcNode.getFuncName(), varChange);
        }
    }

    /**
     * Print IN and OUT variable sets for each statement in each function for debugging
     */
    public void printInOutVars() {
        System.err.println("=== DEBUG: Printing IN/OUT variable sets for each statement ===");
        for (CFGFuncNode funcNode : callGraph.getFuncNodes()) {
            System.err.println("\nFunction: " + funcNode.getFuncName());
            System.err.println("Parameters: " + funcNode.getParameters());
            System.err.println("---------------------------------------");
            printStmtInOutVars(funcNode.getRoot(), 0);
        }
        System.err.println("\n=== DEBUG: Printing completed ===\n");
    }

    /**
     * Recursively print IN and OUT variable sets for statement nodes
     * @param stmt statement node
     * @param depth indentation depth
     */
    private void printStmtInOutVars(CFGStmtNode stmt, int depth) {
        // Generate indentation
        String indent = "";
        for (int i = 0; i < depth; i++) {
            indent += "  ";
        }
        
        // Print statement information
        System.err.println(indent + "Statement [" + stmt.getType() + "]: " + 
                          (stmt.getContent().length() > 80 ? 
                           stmt.getContent().substring(0, 80) + "..." : 
                           stmt.getContent()));
        
        // Print IN variable set
        System.err.println(indent + "  IN:  " + formatVarSet(stmt.InVar));
        
        // Print OUT variable set
        System.err.println(indent + "  OUT: " + formatVarSet(stmt.OutVar));
        
        // Print temporary variables if any
        if (stmt.getTemporaryVariables() != null && !stmt.getTemporaryVariables().isEmpty()) {
            Set<String> tempVarSet = new HashSet<>(stmt.getTemporaryVariables());
            System.err.println(indent + "  TEMP: " + formatVarSet(tempVarSet));
        }
        
        System.err.println(indent + "  ---");
        
        // Recursively print child nodes
        for (CFGStmtNode child : stmt.getChildren()) {
            printStmtInOutVars(child, depth + 1);
        }
    }

    /**
     * Format variable set as string for printing
     * @param varSet variable set
     * @return formatted string
     */
    private String formatVarSet(Set<String> varSet) {
        if (varSet == null || varSet.isEmpty()) {
            return "{}";
        }
        
        List<String> sortedVars = new ArrayList<>(varSet);
        Collections.sort(sortedVars);
        
        StringBuilder sb = new StringBuilder();
        sb.append("{");
        for (int i = 0; i < sortedVars.size(); i++) {
            if (i > 0) sb.append(", ");
            sb.append(sortedVars.get(i));
        }
        sb.append("}");
        
        return sb.toString();
    }

    /**
     * Print function variable change information for debugging
     */
    public void printFuncVarChange() {
        System.err.println("\n=== DEBUG: Printing function variable change information ===");
        for (String funcName : callGraph.getFuncNames()) {
            Set<String> varChange = funcVarChange.get(funcName);
            System.err.println("Function " + funcName + " changed variables: " + formatVarSet(varChange));
        }
        System.err.println("=== DEBUG: Function variable change information completed ===\n");
    }

    /**
     * Print cut function information for debugging
     */
    public void printCuttedFuncInfo() {
        System.err.println("\n=== DEBUG: Printing cut function information ===");
        System.err.println("Number of cut functions: " + cuttedFunc.size());
        for (CFGFuncNode funcNode : cuttedFunc) {
            System.err.println("  - " + funcNode.getFuncName());
        }
        
        System.err.println("Number of root functions: " + (rootFunc != null ? rootFunc.size() : 0));
        if (rootFunc != null) {
            for (CFGFuncNode funcNode : rootFunc) {
                System.err.println("  - " + funcNode.getFuncName());
            }
        }
        
        Set<String> uncalledFunc = getUncalledFunc();
        System.err.println("Number of uncalled functions: " + uncalledFunc.size());
        for (String funcName : uncalledFunc) {
            System.err.println("  - " + funcName);
        }
        System.err.println("=== DEBUG: Cut function information completed ===\n");
    }

    /**
     * Print detected variables for debugging
     */
    public void printDetectedVariables() {
        System.err.println("\n=== DEBUG: Detected Variables ===");
        System.err.println("Total variables detected: " + variables.size());
        for (String var : variables) {
            System.err.println("  - " + var);
        }
        System.err.println("=== DEBUG: Variables list completed ===\n");
    }

    private void clearUNCHANGED(){
        for (CFGFuncNode funcNode : callGraph.getAllFuncNodes()) {
            clearUNCHANGEDHelper(funcNode.getRoot());
        }
    }
    
    /**
     * Recursively traverse statement nodes, clear all UNCHANGED statements
     * @param stmtNode statement node
     */
    private void clearUNCHANGEDHelper(CFGStmtNode stmtNode) {
        if (stmtNode == null) {
            return;
        }
        
        // Check if the current statement contains UNCHANGED    
        String content = stmtNode.getContent();
        if (content != null && content.contains("UNCHANGED")) {
            // Clear UNCHANGED statement to placeholder
            String newContent = replaceUNCHANGEDContent(content);
            stmtNode.setContent(newContent);
        }
        
        // Recursively process all child nodes
        if (stmtNode.getChildren() != null) {
            for (CFGStmtNode child : stmtNode.getChildren()) {
                clearUNCHANGEDHelper(child);
            }
        }
    }
    
    /**
     * Replace UNCHANGED content in statement
     * @param content original statement content
     * @return replaced statement content
     */
    private String replaceUNCHANGEDContent(String content) {
        // Handle UNCHANGED << ... >> format
        String result = content.replaceAll("UNCHANGED\\s*<<[^<>]*>>", "UNCHANGED <<>>");
        
        // Handle UNCHANGED var format (single variable or alias)
        result = result.replaceAll("UNCHANGED\\s+\\w+", "UNCHANGED <<>>");
        
        return result;
    }
}