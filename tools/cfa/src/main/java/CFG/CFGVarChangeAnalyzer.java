package CFG;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Iterator;
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
        prepareForSAPass();
        // System.err.println("begin analyze");
        // Get topological sequence
        List<CFGFuncNode> topologicalSort = callGraph.getTopologicalSort();
        // Reverse
        Collections.reverse(topologicalSort);
        for (CFGFuncNode funcNode : topologicalSort) {
            // Analyze each function
            analyzeFuncSA(funcNode);
        }
        //traverseTree();
        for (CFGFuncNode funcNode : topologicalSort){
            checkCuttedFunc(funcNode);
        }

        List<CFGFuncNode> funcNodes = new ArrayList<>(callGraph.getFuncNodes());
        WorkList.addAll(funcNodes);
        while (!WorkList.isEmpty()){
            tempVars = new HashSet<>();
            CFGFuncNode funcNode = WorkList.remove(0);
            if (funcNode.isEntryPoint()){
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
            if (funcNode.isEntryPoint()){
                genHandleUncalledFunc(funcNode);
            } else {
                genHandleCalledFunc(funcNode);
            }
        }

        // Note: Auxiliary variables (pc, stack, info) are already added to callGraph
        // in SANYTransformerCli before constructing CFGVarChangeAnalyzer

        analyzeUC();
        // UD pass temporarily disabled pending redesign.
    }

    public void analyze_only_sa(){
        prepareForSAPass();
        List<CFGFuncNode> topologicalSort = callGraph.getTopologicalSort();
        // Reverse
        Collections.reverse(topologicalSort);
        for (CFGFuncNode funcNode : topologicalSort) {
            analyzeFuncSA(funcNode);
        }
    }

    public void analyze_only_pc(){
        prepareForSAPass();
        // Get topological sequence
        List<CFGFuncNode> topologicalSort = callGraph.getTopologicalSort();
        // Reverse
        Collections.reverse(topologicalSort);
        for (CFGFuncNode funcNode : topologicalSort) {
            // Analyze each function
            analyzeFuncSA(funcNode);
        }
        for (CFGFuncNode funcNode : topologicalSort){
            checkCuttedFunc(funcNode);
        }

        List<CFGFuncNode> funcNodes = new ArrayList<>(callGraph.getFuncNodes());
        WorkList.addAll(funcNodes);
        while (!WorkList.isEmpty()){
            tempVars = new HashSet<>();
            CFGFuncNode funcNode = WorkList.remove(0);
            if (funcNode.isEntryPoint()){
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
            if (funcNode.isEntryPoint()){
                genHandleUncalledFunc(funcNode);
            } else {
                genHandleCalledFunc(funcNode);
            }
        }
    }

    public void analyze_only_ud(){
        throw new UnsupportedOperationException("UD pass is temporarily disabled");
    }

    public void analyze_only_uc(){
        prepareForSAPass();
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
        if (stmtNode == null) {
            return;
        }
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
        newFuncNode.setInvocationKind(CFGFuncNode.InvocationKind.ENTRY);
        CFGStmtNode root = new CFGStmtNode(0, "root", null, CFGStmtNode.StmtType.ROOT);
        newFuncNode.setRoot(root);
        funcVarChange.putIfAbsent(newFuncNode.getFuncName(), new HashSet<>());
        CFGStmtNode pc_stmt = new CFGStmtNode(1, "pc = Nil", null, CFGStmtNode.StmtType.NORMAL);
        root.addChild(pc_stmt);
        CFGStmtNode call_stmt = new CFGStmtNode(1, Call_uncalled(funcNode), null, CFGStmtNode.StmtType.NORMAL);
        pc_stmt.addChild(call_stmt); 
        Set<String> unchangedVar = new HashSet<>(variables);
        unchangedVar.removeAll(funcVarChange.get(funcNode.getFuncName()));
        CFGStmtNode unchanged_stmt = new CFGStmtNode(1, getUnchangedVar(unchangedVar), null, CFGStmtNode.StmtType.NORMAL);
        call_stmt.addChild(unchanged_stmt);
        callGraph.addFuncNode(newFuncNode);
        callGraph.addFuncName(newFuncNode.getFuncName());
        CFGCALLEdge callEdge = new CFGCALLEdge(call_stmt, newFuncNode, funcNode, null, null);
        callGraph.addCallEdge(callEdge);
        CFGStmtNode stack_stmt = new CFGStmtNode(1, "stack' = <<[backsite |-> Nil, info |-> [args |-> <<>>, temp |-> <<>>], args |-> <<>>]>>", null, CFGStmtNode.StmtType.NORMAL);
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
            newFuncNode.setInvocationKind(CFGFuncNode.InvocationKind.ENTRY);
            CFGStmtNode root = new CFGStmtNode(0, "root", null, CFGStmtNode.StmtType.ROOT);
            newFuncNode.setRoot(root);
            funcVarChange.putIfAbsent(newFuncNode.getFuncName(), new HashSet<>());
            CFGStmtNode pc_stmt = new CFGStmtNode(1, "pc = \"" + funcNode.getFuncName() + "\"", null, CFGStmtNode.StmtType.NORMAL);
            root.addChild(pc_stmt);
            CFGStmtNode call_stmt;
            if (funcNode.isEntryPoint()){
                call_stmt = new CFGStmtNode(1, Call_root_called(funcNode), null, CFGStmtNode.StmtType.NORMAL);
            } else {
                call_stmt = new CFGStmtNode(1, Call_nonroot_called(funcNode), null, CFGStmtNode.StmtType.NORMAL);
            }
            pc_stmt.addChild(call_stmt);
        Set<String> unchangedVar = new HashSet<>(variables);
        unchangedVar.removeAll(funcVarChange.get(funcNode.getFuncName()));
        CFGStmtNode unchanged_stmt = new CFGStmtNode(1, getUnchangedVar(unchangedVar), null, CFGStmtNode.StmtType.NORMAL);
            call_stmt.addChild(unchanged_stmt);
            callGraph.addFuncNode(newFuncNode);
            callGraph.addFuncName(newFuncNode.getFuncName());
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
        List<CFGFuncNode> targetFunc = Collections.emptyList();
        String targetFuncName = null;
        if (stmt.getType() == CFGStmtNode.StmtType.CALL){
            targetFunc = callGraph.getTargetFunc(stmt);
            for (CFGFuncNode targetFuncNode : targetFunc){
                declVar.addAll(funcVarChange.get(targetFuncNode.getFuncName()));
                if (cuttedFunc.contains(targetFuncNode)){
                    flag = true;
                }
            }
            if (targetFunc.size() == 1) {
                targetFuncName = targetFunc.get(0).getFuncName();
            }
        }
        declVar.addAll(VarChangedOneStmt(stmt));
        intersection.retainAll(declVar);
        // Discuss by cases:
        if (flag) {
            // If already cut, need to cut this function
            int id = funcNode.getIDandADD();
            CFGFuncNode newFuncNode = new CFGFuncNode(funcNode.getFuncName() + "_" + id, funcNode.getParameters(), id);
            newFuncNode.setInvocationKind(CFGFuncNode.InvocationKind.CALLED);
            funcVarChange.putIfAbsent(newFuncNode.getFuncName(), new HashSet<>());
            CFGStmtNode root = new CFGStmtNode(0, "root", null, CFGStmtNode.StmtType.ROOT);
            newFuncNode.setRoot(root);

            CFGStmtNode startStmt;
            if (!stmt.getChildren().isEmpty()) {
                startStmt = stmt.getChildren().get(0).copyTree(callGraph, newFuncNode);
            } else {
                startStmt = new CFGStmtNode(stmt.getIndentation(), "TRUE", null, CFGStmtNode.StmtType.NORMAL);
                startStmt.setSynthetic(true);
            }
            root.addChild(startStmt);

            Set<CFGStmtNode> parents = funcNode.getAllparents(stmt);
            CFGFuncNode pushFuncNode = null;
            String parentPcTarget;
            targetFuncName = targetFunc.size() == 1 ? targetFunc.get(0).getFuncName() : null;
            if (funcNode.isEntryPoint()) {
                if (targetFuncName == null) {
                    throw new RuntimeException("Multi-function call variable modification conflict: " + targetFunc);
                }
                pushFuncNode = createEntryPushFunction(funcNode, newFuncNode, targetFuncName, stmt, tempVarsThisFunc, targetFuncName);
                parentPcTarget = pushFuncNode.getFuncName();
            } else {
                if (targetFuncName != null){
                    parentPcTarget = targetFuncName;
                } else {
                    throw new RuntimeException("Multi-function call variable modification conflict: " + targetFunc);
                }
            }
            CFGStmtNode pc_jump = new CFGStmtNode(stmt.getIndentation(), "pc' = \"" + parentPcTarget + "\"", null, CFGStmtNode.StmtType.NORMAL);
            pc_jump.InVar = new HashSet<>(stmt.InVar);
            pc_jump.OutVar = new HashSet<>(stmt.InVar);
            pc_jump.OutVar.add("pc");
            for (CFGStmtNode parent : parents){
                int childIndex = parent.getChildren().indexOf(stmt);
                parent.replaceChild(childIndex, pc_jump);
                List<CFGStmtNode> parentList = parentMap.get(stmt);
                if (parentList != null) {
                    parentList.remove(parent);
                    if (parentList.isEmpty()) {
                        parentMap.remove(stmt);
                    }
                }
                parentMap.computeIfAbsent(pc_jump, k -> new ArrayList<>()).add(parent);
            }

            callGraph.addFuncNode(newFuncNode);
            callGraph.addFuncName(newFuncNode.getFuncName());
            updateNewFuncCallEdge(newFuncNode, root);
            resetInOutVar(root);
            analyzeFuncSA(newFuncNode);
            WorkList.add(newFuncNode);
            cuttedFunc.add(newFuncNode);

            if (!funcNode.isEntryPoint()){
                CFGStmtNode info_node = new CFGStmtNode(stmt.getIndentation(), updateInfoStr(tempVarsThisFunc), null, CFGStmtNode.StmtType.NORMAL);
                info_node.InVar = new HashSet<>(pc_jump.OutVar);
                info_node.OutVar = new HashSet<>(pc_jump.OutVar);
                info_node.OutVar.add("info");
                pc_jump.addChild(info_node);
                parentMap.computeIfAbsent(info_node, k -> new ArrayList<>()).add(pc_jump);

                CFGStmtNode stack_node = new CFGStmtNode(stmt.getIndentation(), updateStackStr(newFuncNode, stmt.getContent(), targetFuncName), null, CFGStmtNode.StmtType.NORMAL);
                stack_node.InVar = new HashSet<>(info_node.OutVar);
                stack_node.OutVar = new HashSet<>(info_node.OutVar);
                stack_node.OutVar.add("stack");
                info_node.addChild(stack_node);
                parentMap.computeIfAbsent(stack_node, k -> new ArrayList<>()).add(info_node);
            }

            updateNewFuncTempVars(newFuncNode, tempVarsThisFunc);
            if (pushFuncNode != null) {
                callGraph.addFuncNode(pushFuncNode);
                callGraph.addFuncName(pushFuncNode.getFuncName());
                updateNewFuncCallEdge(pushFuncNode, pushFuncNode.getRoot());
                resetInOutVar(pushFuncNode.getRoot());
                analyzeFuncSA(pushFuncNode);
                WorkList.add(pushFuncNode);
            }
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
                    if ((cuttedFunc.contains(funcNode) && funcNode.getInvocationKind() == CFGFuncNode.InvocationKind.CALLED) && !stmt.getContent().contains("info' =") && !stmt.getContent().contains("stack' =")){
                        CFGStmtNode pc_stmt = new CFGStmtNode(stmt.getIndentation(), "pc' = stack[Len(stack)].backsite", null, CFGStmtNode.StmtType.NORMAL);
                        pc_stmt.InVar = new HashSet<>(stmt.OutVar);
                        pc_stmt.OutVar = new HashSet<>(stmt.OutVar);
                        pc_stmt.OutVar.add("pc");
                        stmt.addChild(pc_stmt);
                        parentMap.computeIfAbsent(pc_stmt, k -> new ArrayList<>()).add(stmt);
                        CFGStmtNode stack_node = new CFGStmtNode(stmt.getIndentation(), "stack' = Tail(stack)", null, CFGStmtNode.StmtType.NORMAL);
                        stack_node.InVar = new HashSet<>(pc_stmt.OutVar);
                        stack_node.OutVar = new HashSet<>(pc_stmt.OutVar);
                        stack_node.OutVar.add("stack");
                        pc_stmt.addChild(stack_node);
                        parentMap.computeIfAbsent(stack_node, k -> new ArrayList<>()).add(pc_stmt);
                        CFGStmtNode info_node = new CFGStmtNode(stmt.getIndentation(), "info' = stack[Len(stack)].info", null, CFGStmtNode.StmtType.NORMAL);
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
                newFuncNode.setInvocationKind(CFGFuncNode.InvocationKind.CALLED);
                funcVarChange.putIfAbsent(newFuncNode.getFuncName(), new HashSet<>());
                CFGStmtNode root = new CFGStmtNode(0, "root", null, CFGStmtNode.StmtType.ROOT);
                newFuncNode.setRoot(root);
                // Cut
                Set<CFGStmtNode> parents = funcNode.getAllparents(stmt);
                CFGStmtNode pc_stmt_copy = stmt.copyTree(callGraph, newFuncNode);
                root.addChild(pc_stmt_copy);
                // Generate pc' target for continuation
                CFGFuncNode pushFuncNode = null;
                String parentPcTarget;
                if (funcNode.isEntryPoint()) {
                    pushFuncNode = createEntryPushFunction(funcNode, newFuncNode, targetFuncName, stmt, tempVarsThisFunc, newFuncNode.getFuncName());
                    parentPcTarget = pushFuncNode.getFuncName();
                } else {
                    parentPcTarget = funcNode.getFuncName() + "_" + id;
                }
                CFGStmtNode pc_jump = new CFGStmtNode(stmt.getIndentation(), "pc' = \"" + parentPcTarget + "\"", null, CFGStmtNode.StmtType.NORMAL);
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
                    int childIndex = parent.getChildren().indexOf(stmt);
                    parent.replaceChild(childIndex, pc_jump);
                    List<CFGStmtNode> parentList = parentMap.get(stmt);
                    if (parentList != null) {
                        parentList.remove(parent);
                        if (parentList.isEmpty()) {
                            parentMap.remove(stmt);
                        }
                    }
                    parentMap.computeIfAbsent(pc_jump, k -> new ArrayList<>()).add(parent);
                }
                callGraph.addFuncNode(newFuncNode);
                callGraph.addFuncName(newFuncNode.getFuncName());
                updateNewFuncCallEdge(newFuncNode, root);
                // New InVar OutVar is cleared
                resetInOutVar(root);
                // Generated function also needs to be analyzed, added to subsequent Worklist
                analyzeFuncSA(newFuncNode);
                WorkList.add(newFuncNode);
                cuttedFunc.add(newFuncNode);
                if (!funcNode.isEntryPoint()){
                    CFGStmtNode info_node = new CFGStmtNode(stmt.getIndentation(), updateInfoStr(tempVarsThisFunc), null, CFGStmtNode.StmtType.NORMAL);
                    info_node.InVar = new HashSet<>(pc_jump.OutVar);
                    info_node.OutVar = new HashSet<>(pc_jump.OutVar);
                    info_node.OutVar.add("info");
                    pc_jump.addChild(info_node);
                    parentMap.computeIfAbsent(info_node, k -> new ArrayList<>()).add(pc_jump);
                    CFGStmtNode stack_node = new CFGStmtNode(stmt.getIndentation(), updateStackStr(newFuncNode, stmt.getContent(), targetFuncName), null, CFGStmtNode.StmtType.NORMAL);
                    stack_node.InVar = new HashSet<>(info_node.OutVar);
                    stack_node.OutVar = new HashSet<>(info_node.OutVar);
                    stack_node.OutVar.add("stack");
                    info_node.addChild(stack_node);
                    parentMap.computeIfAbsent(stack_node, k -> new ArrayList<>()).add(info_node);
                }
                // Change temporary variables in new function to variables in info
                updateNewFuncTempVars(newFuncNode, tempVarsThisFunc);
                if (pushFuncNode != null) {
                    callGraph.addFuncNode(pushFuncNode);
                    callGraph.addFuncName(pushFuncNode.getFuncName());
                    updateNewFuncCallEdge(pushFuncNode, pushFuncNode.getRoot());
                    resetInOutVar(pushFuncNode.getRoot());
                    analyzeFuncSA(pushFuncNode);
                    WorkList.add(pushFuncNode);
                }
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
                    String unchangedVar = "UNCHANGED <<";
                    boolean first = true;
                    for (String var : diff) {
                        if (!first) {
                            unchangedVar += ", ";
                        }
                        unchangedVar += var;
                        first = false;
                    }
                    unchangedVar += ">>";
                    CFGStmtNode newStmt = new CFGStmtNode(parent.getIndentation(), unchangedVar, null, CFGStmtNode.StmtType.UNCHANGED);
                    newStmt.setSynthetic(true);
                    newStmt.InVar = parent.OutVar;
                    newStmt.OutVar = stmt.InVar;
                    int childIndex = parent.getChildren().indexOf(stmt);
                    parent.replaceChild(childIndex, newStmt);
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
                    String unchangedVar = "UNCHANGED <<";
                    boolean first = true;
                    for (String var : diff) {
                    if (!first) {
                        unchangedVar += ", ";
                    }
                    unchangedVar += var;
                    first = false;
                }
                unchangedVar += ">>";
                CFGStmtNode newStmt = new CFGStmtNode(leafNode.getIndentation(), unchangedVar, null, CFGStmtNode.StmtType.UNCHANGED);
                newStmt.setSynthetic(true);
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
        if (content == null || content.isEmpty()) {
            return result;
        }

        // Detect explicit next-state assignments such as x' = ..., x' \in ...
        for (String var : variables) {
            String primePattern = "(?s)(?<![\\w_])" + Pattern.quote(var) + "'\\s*(=|\\\\in|\\\\subseteq)";
            if (Pattern.compile(primePattern, Pattern.DOTALL).matcher(content).find()) {
                result.add(var);
            }
        }

        // Handle UNCHANGED statements (treat as writing primes for SA purposes)
        if (content.contains("UNCHANGED")) {
            // Match UNCHANGED << ... >> with possible newlines/spacing
            Pattern unchangedListPattern = Pattern.compile("(?s)UNCHANGED\\s*<<([^<>]*)>>");
            java.util.regex.Matcher listMatcher = unchangedListPattern.matcher(content);
            while (listMatcher.find()) {
                String varsSegment = listMatcher.group(1);
                for (String candidate : varsSegment.split(",")) {
                    String trimmed = candidate.trim();
                    if (trimmed.isEmpty()) {
                        continue;
                    }
                    collectUnchangedTarget(trimmed, result);
                }
            }

            // Match single-variable UNCHANGED (ensure not followed by <<)
            Pattern unchangedSinglePattern = Pattern.compile("(?s)UNCHANGED\\s+(?!<<)([^\\s]+)");
            java.util.regex.Matcher singleMatcher = unchangedSinglePattern.matcher(content);
            while (singleMatcher.find()) {
                String target = singleMatcher.group(1).trim();
                if (!target.isEmpty()) {
                    collectUnchangedTarget(target, result);
                }
            }
        }

        return result;
    }

    private void collectUnchangedTarget(String token, Set<String> result) {
        if (variables.contains(token)) {
            result.add(token);
        } else if (callGraph.isAlias(token)) {
            List<String> resolvedVars = callGraph.resolveAlias(token);
            if (resolvedVars != null) {
                result.addAll(resolvedVars);
            }
        }
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
        List<CFGStmtNode> parents = parentMap.computeIfAbsent(stmt, k -> new ArrayList<>());
        if (!parents.contains(parent)) {
            parents.add(parent);
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

    private void prepareForSAPass() {
        clearAllUNCHANGEDStatements();  // Remove ALL UNCHANGED (both synthetic and from source)
        parentMap.clear();
        for (CFGFuncNode funcNode : callGraph.getAllFuncNodes()) {
            CFGStmtNode root = funcNode.getRoot();
            if (root != null) {
                resetInOutVar(root);
            }
        }
    }

    public void checkCuttedFunc(CFGFuncNode funcNode){
        for (CFGStmtNode stmt : funcNode.getRoot().getChildren()){
            checkCuttedFuncHelper(funcNode, stmt);
        }
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
        String unchangedVar = "UNCHANGED <<";
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
        String infoStr = "info' = [";
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
        String infoStr = "info' = ";
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

    private String updateStackStr(CFGFuncNode continuationNode, String callsite, String calleeName){
        String arguments = "<< ";
        int start = -1;
        int end = -1;
        if (calleeName != null && !calleeName.isEmpty()) {
            String pattern = calleeName + "(";
            start = callsite.indexOf(pattern);
            if (start != -1) {
                start += pattern.length() - 1; // position of '('
            }
        }
        if (start == -1) {
            start = callsite.indexOf("(");
        }
        // Check if '(' is found
        if (start != -1) {
            int depth = 0;
            for (int i = start; i < callsite.length(); i++) {
                char c = callsite.charAt(i);
                if (c == '(') {
                    depth++;
                } else if (c == ')') {
                    depth--;
                    if (depth == 0) {
                        end = i;
                        break;
                    }
                }
            }
            if (end != -1 && end > start) {
                arguments += callsite.substring(start + 1, end).trim();
            }
        }
        // If parsing failed, arguments remain empty
        arguments += ">>";
        String stackStr = "stack' = Append(stack, [backsite |-> \"" + continuationNode.getFuncName() + "\", args |-> " + arguments + ", info |-> info'])";
        return stackStr;
    }

    private CFGFuncNode createEntryPushFunction(CFGFuncNode funcNode, CFGFuncNode continuationNode, String calleeName, CFGStmtNode originalStmt, Set<String> tempVarsThisFunc, String nextPc) {
        String pushFuncName = funcNode.getFuncName() + "_push_" + continuationNode.getID();
        CFGFuncNode pushFuncNode = new CFGFuncNode(pushFuncName, funcNode.getParameters(), continuationNode.getID());
        pushFuncNode.setInvocationKind(CFGFuncNode.InvocationKind.CALLED);
        funcVarChange.putIfAbsent(pushFuncNode.getFuncName(), new HashSet<>());
        CFGStmtNode pushRoot = new CFGStmtNode(0, "root", null, CFGStmtNode.StmtType.ROOT);
        pushFuncNode.setRoot(pushRoot);

        CFGStmtNode infoStmt = new CFGStmtNode(originalStmt.getIndentation(), setInfoStr(funcNode.getParameters(), tempVarsThisFunc), null, CFGStmtNode.StmtType.NORMAL);
        CFGStmtNode stackStmt = new CFGStmtNode(originalStmt.getIndentation(), updateStackStr(continuationNode, originalStmt.getContent(), calleeName), null, CFGStmtNode.StmtType.NORMAL);
        CFGStmtNode pcStmt = new CFGStmtNode(originalStmt.getIndentation(), "pc' = \"" + nextPc + "\"", null, CFGStmtNode.StmtType.NORMAL);

        pushRoot.addChild(infoStmt);
        infoStmt.addChild(stackStmt);
        stackStmt.addChild(pcStmt);

        return pushFuncNode;
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
                // Pattern to match variable references but NOT record field names
                // Field names in TLA+ records look like: [field |-> value] or , field |-> value
                // We need to avoid replacing "term" in "term |->" but replace "term" in "-> term"
                String pattern = "(?<!\\w)(?<!info\\.temp\\.)" + var + "(?!\\w)(?!\\s*\\|->)";

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
            funcNode.setPureExpression(varChange.isEmpty());
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

        int entryCount = 0;
        int calledCount = 0;
        for (CFGFuncNode funcNode : callGraph.getFuncNodes()) {
            if (funcNode.isEntryPoint()) {
                entryCount++;
            } else {
                calledCount++;
            }
        }
        System.err.println("Number of entry functions: " + entryCount);
        System.err.println("Number of called functions: " + calledCount);
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

    private void clearSyntheticUNCHANGED() {
        removeUNCHANGEDNodes(true);
    }

    public void clearAllUNCHANGEDStatements() {
        removeUNCHANGEDNodes(false);
    }

    private void removeUNCHANGEDNodes(boolean syntheticOnly) {
        for (CFGFuncNode funcNode : callGraph.getAllFuncNodes()) {
            removeUNCHANGEDHelper(funcNode.getRoot(), syntheticOnly);
        }
    }
    
    private void removeUNCHANGEDHelper(CFGStmtNode stmtNode, boolean syntheticOnly) {
        if (stmtNode == null) {
            return;
        }
        List<CFGStmtNode> children = stmtNode.getChildren();
        if (children == null || children.isEmpty()) {
            return;
        }

        // Check if current node is a branch statement
        boolean isBranchStatement = stmtNode.getType() == CFGStmtNode.StmtType.IF_ELSE ||
                                   stmtNode.getType() == CFGStmtNode.StmtType.CASE ||
                                   stmtNode.getType() == CFGStmtNode.StmtType.DISJUNCTION;

        for (int i = 0; i < children.size();) {
            CFGStmtNode child = children.get(i);
            boolean isTarget = child.getType() == CFGStmtNode.StmtType.UNCHANGED;
            if (isTarget && (!syntheticOnly || child.isSynthetic())) {
                if (isBranchStatement) {
                    // If parent is a branch statement, replace with empty UNCHANGED
                    child.setContent("UNCHANGED <<>>");
                    i++;
                } else {
                    // Otherwise, remove the node and promote its children
                    List<CFGStmtNode> grandChildren = new ArrayList<>(child.getChildren());
                    children.remove(i);
                    if (!grandChildren.isEmpty()) {
                        children.addAll(i, grandChildren);
                    }
                    // Do not increment i so we process newly inserted grandchildren (if any)
                    continue;
                }
            } else {
                removeUNCHANGEDHelper(child, syntheticOnly);
                i++;
            }
        }
    }
}
