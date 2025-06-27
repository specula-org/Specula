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
        // 得到拓扑序列
        List<CFGFuncNode> topologicalSort = callGraph.getTopologicalSort();
        //反过来
        Collections.reverse(topologicalSort);
        for (CFGFuncNode funcNode : topologicalSort) {
            // 对每个函数进行分析
            analyzeFuncSA(funcNode);
        }
        //traverseTree();
        // 计算 CallGraph 中未被调用的函数
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

        // 更新 funcVarChange
        updateFuncVarChange();
        List<CFGFuncNode> funclist = new ArrayList<>(callGraph.getFuncNodes());
        // 生成 handle 函数
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
    // 静态分析构建父亲节点映射关系和 IN 和 OUT
    private void analyzeFuncSA(CFGFuncNode funcNode){
        CFGStmtNode stmtNode = funcNode.getRoot();
        buildParentMap(stmtNode);
        for (CFGStmtNode stmt : stmtNode.getChildren()) {
            analyzeStmtSA(funcNode, stmt, stmtNode.OutVar);
        }
        // 控制流汇聚点处理前，建立父亲关系
        funcVarChange.put(funcNode.getFuncName(), getAllLeafVar(stmtNode));
    }


    private void analyzeStmtSA(CFGFuncNode funcNode, CFGStmtNode stmt, Set<String> OutVar){
        // 静态分析
        // 遍历调用的函数，记录改变的变量，检测冲突
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
                    throw new RuntimeException("多函数调用变量修改冲突: " + VarDecl + " " + targetFuncNode.getFuncName() +  "  " + stmt.getContent() + "  " + funcNode.getFuncName());
                }
            }
            VarDecl.addAll(VarChanged);
        }
        // Stmt 改变的变量，检测冲突
        Set<String> VarChangedStmt = VarChangedOneStmt(stmt);
        Set<String> intersection = new HashSet<>(VarChangedStmt);
        intersection.retainAll(VarDecl);
        if (!intersection.isEmpty()){
            // 报错时打印 VarChangedStmt 和 VarDecl
            // System.err.println("VarChangedStmt: " + VarChangedStmt);
            // System.err.println("VarDecl: " + VarDecl);
            throw new RuntimeException("多函数调用变量修改冲突: " + intersection + " "+ stmt.getContent());
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
        // uncalled 一定是 root
        // HandleFunc(args) == 
        //      /\ pc = Nil
        //      /\ func(args)
        //      /\ UNCHANGED <<vars - Vars_func>>
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
    }

    private void genHandleCalledFunc(CFGFuncNode funcNode){
        // Func 未被切割：直接返回
        // Func 被切割：
        // HandleFunc(args) == 
        //      /\ pc = funcname
        //      /\ func(stack.args)
        //      /\ UNCHANGED <<vars - Vars_func>>
        if (cuttedFunc.contains(funcNode)){
            // 被切割
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
        // 分情况讨论：
        if (flag) {
            // 如果已经切分过，则需要切分本函数
            int id = funcNode.getIDandADD();
            CFGFuncNode newFuncNode = new CFGFuncNode(funcNode.getFuncName() + "_" + id, funcNode.getParameters(), id);
            CFGStmtNode root = new CFGStmtNode(0, "root", null, CFGStmtNode.StmtType.ROOT);
            newFuncNode.setRoot(root);
            CFGStmtNode start_stmt = null;
            if (!stmt.getChildren().isEmpty()){
                // 将 stmt 的子节点作为新函数的第一个节点，后续节点全部 copy 形成新函数
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
                // 报错：暂时不支持
                throw new RuntimeException("多函数调用变量修改冲突: " + targetFunc);
            }
            // pc' = name
            // info' = [args |-> <<>>, temp |-> [temp1 |-> temp1, temp2 |-> temp2, ...]]
            // stack'= [backsite |-> newfuncname, args |-> <<>>, info |-> info']
            pc_jump.InVar = new HashSet<>(stmt.InVar);
            pc_jump.OutVar = new HashSet<>(stmt.InVar);
            pc_jump.OutVar.add("pc");
            // 将 pc_jump 添加
            for (CFGStmtNode parent : parents){
                parent.deleteChild(stmt);
                parent.addChild(pc_jump);
                parentMap.computeIfAbsent(pc_jump, k -> new ArrayList<>()).add(parent);
            }
            updateNewFuncCallEdge(newFuncNode, root);
            // 新生成的 InVar OutVar 清空
            resetInOutVar(root);
            // 生成的函数同样需要分析，加到后续的 Worklist 中
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
            // 将新函数中的临时变量改为 info 中的变量
            updateNewFuncTempVars(newFuncNode, tempVarsThisFunc);
        } else {
            //如果没有切分过，没冲突则不需要切割，有冲突仍需要切割
            if (intersection.isEmpty()){
                // 没冲突，不需要切割
                List<CFGStmtNode> children = new ArrayList<>(stmt.getChildren());
                if (!children.isEmpty()){
                    for (CFGStmtNode child : children){
                        tempVars = new HashSet<>(tempVarsThisFunc);
                        analyzeStmtPC(funcNode, child);
                    }
                } else {
                    // 没有子节点，是返回的节点，那么需要退栈
                    //     pc' = stack.backsite
                    //     info' = stack.info
                    //     stack' = Head(stack)
                    Set<String> uncalledFunc = getUncalledFunc();
                    if ((cuttedFunc.contains(funcNode) && !uncalledFunc.contains(funcNode.getFuncName())) && !stmt.getContent().contains("/\\ info' =") && !stmt.getContent().contains("/\\ stack' =")){
                        CFGStmtNode pc_stmt = new CFGStmtNode(stmt.getIndentation(), "/\\ pc' = stack.backsite", null, CFGStmtNode.StmtType.NORMAL);
                        pc_stmt.InVar = new HashSet<>(stmt.OutVar);
                        pc_stmt.OutVar = new HashSet<>(stmt.OutVar);
                        pc_stmt.OutVar.add("pc");
                        stmt.addChild(pc_stmt);
                        parentMap.computeIfAbsent(pc_stmt, k -> new ArrayList<>()).add(stmt);
                        CFGStmtNode stack_node = new CFGStmtNode(stmt.getIndentation(), "/\\ stack' = Head(stack)", null, CFGStmtNode.StmtType.NORMAL);
                        stack_node.InVar = new HashSet<>(pc_stmt.OutVar);
                        stack_node.OutVar = new HashSet<>(pc_stmt.OutVar);
                        stack_node.OutVar.add("stack");
                        pc_stmt.addChild(stack_node);
                        parentMap.computeIfAbsent(stack_node, k -> new ArrayList<>()).add(pc_stmt);
                        CFGStmtNode info_node = new CFGStmtNode(stmt.getIndentation(), "/\\ info' = stack.info", null, CFGStmtNode.StmtType.NORMAL);
                        info_node.InVar = new HashSet<>(stack_node.OutVar);
                        info_node.OutVar = new HashSet<>(stack_node.OutVar);
                        info_node.OutVar.add("info");
                        stack_node.addChild(info_node);
                        parentMap.computeIfAbsent(info_node, k -> new ArrayList<>()).add(stack_node);
                    }
                }
            } else {
                // 有冲突，需要切割
                // 初始化切割出的函数
                int id = funcNode.getIDandADD();
                CFGFuncNode newFuncNode = new CFGFuncNode(funcNode.getFuncName() + "_" + id, funcNode.getParameters(), id);
                CFGStmtNode root = new CFGStmtNode(0, "root", null, CFGStmtNode.StmtType.ROOT);
                newFuncNode.setRoot(root);
                // 切割
                Set<CFGStmtNode> parents = funcNode.getAllparents(stmt);
                CFGStmtNode pc_stmt_copy = stmt.copyTree(callGraph, newFuncNode);
                root.addChild(pc_stmt_copy);
                // 生成 pc' = <<name, args>>
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
                // 检查所有 parent 的 OutVar 是不是相同，否则报错
                // for (CFGStmtNode parent : parents){
                //     if (!parent.OutVar.equals(stmt.InVar)){
                //         throw new RuntimeException("多函数调用变量修改冲突: " + parent.OutVar + " " + stmt.InVar);
                //     }
                // }
                pc_jump.InVar = new HashSet<>(stmt.InVar);
                pc_jump.OutVar = new HashSet<>(stmt.InVar);
                pc_jump.OutVar.add("pc");
                // 将 pc_jump 添加
                for (CFGStmtNode parent : parents){
                    parent.deleteChild(stmt);
                    parent.addChild(pc_jump);
                    parentMap.computeIfAbsent(pc_jump, k -> new ArrayList<>()).add(parent);
                }
                updateNewFuncCallEdge(newFuncNode, root);
                // 新生成的 InVar OutVar 清空
                resetInOutVar(root);
                // 生成的函数同样需要分析，加到后续的 Worklist 中
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
                // 将新函数中的临时变量改为 info 中的变量
                updateNewFuncTempVars(newFuncNode, tempVarsThisFunc);
            }
        }
    }

    private void analyzeUC(){
        // 遍历所有函数，进行分析
        for (CFGFuncNode funcNode : callGraph.getFuncNodes()){
            analyzeFuncUC(funcNode);
        }
    }
 
    private void analyzeFuncUC(CFGFuncNode funcNode){
        //遍历多个父节点的节点
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
                    // 创建 CFGStmtNode 节点
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
                    // 更新 parentMap，将 stmt 的父节点去掉 parent,增加 newStmt
                    parentMap.computeIfAbsent(stmt, k -> new ArrayList<>()).remove(parent);
                    parentMap.computeIfAbsent(stmt, k -> new ArrayList<>()).add(newStmt);
                    parentMap.computeIfAbsent(newStmt, k -> new ArrayList<>()).add(parent);
                }
            }
        }
        // 控制流结束处处理
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
                // 创建 CFGStmtNode 节点
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
        
        // 处理当前节点的内容
        String content = stmtNode.getContent();
        for (String var : stmtNode.InVar) {
            Set<String> skip_set = new HashSet<String>(Arrays.asList("info", "pc", "stack"));
            if (skip_set.contains(var)) {
                continue;
            }
            // 构建正则表达式：变量前后不能是字母数字下划线，且后面不能有'
            String pattern = "(?<![\\w_])" + var + "(?!')(?![\\w_])";
            if (content.matches(".*" + pattern + ".*")) {
                // 替换变量，在后面加上'

                content = content.replaceAll(pattern, var + "'");
            }
        }
        stmtNode.setContent(content);
        
        // 递归处理子节点
        for (CFGStmtNode child : stmtNode.getChildren()) {
            analyzeStmtUD(funcNode, child, stmtUD);
        }
    }

    public Set<String> VarChangedOneStmt(CFGStmtNode stmt) {
        Set<String> result = new HashSet<>();
        for (String var : variables) {
            String pattern = "(?<![\\w_])" + var + "'\\s*=";
            if (stmt.getContent().matches(".*" + pattern + ".*")) {
                result.add(var);
            }
        }
        // 处理 UNCHANGED 语句
        if (stmt.getContent().contains("UNCHANGED")) {
            // 提取 UNCHANGED << >> 中的变量
            if (stmt.getContent().contains("<<")){
                int start = stmt.getContent().indexOf("<<");
                int end = stmt.getContent().indexOf(">>");
                if (start != -1 && end != -1) {
                    String vars = stmt.getContent().substring(start + 2, end);
                    String[] varArray = vars.split(",");
                    for (String var : varArray) {
                        String trimmedVar = var.trim();
                        if (variables.contains(trimmedVar)) {
                            result.add(trimmedVar);
                        }
                    }
                }
            } else {
                // 只有一个变量，将 UNCHANGED 后面的字符保存下来去掉空格即可
                int start = stmt.getContent().indexOf("UNCHANGED");
                String var = stmt.getContent().substring(start + 9).trim();
                if (variables.contains(var)) {
                    result.add(var);
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
        // 创建一个辅助方法，使用Set跟踪已访问节点
        Set<CFGStmtNode> visited = new HashSet<>();
        List<CFGStmtNode> result = new ArrayList<>();
        getAllLeafNodeHelper(stmt, result, visited);
        return result;
    }

    private void getAllLeafNodeHelper(CFGStmtNode stmt, List<CFGStmtNode> result, Set<CFGStmtNode> visited) {
        // 如果已经访问过此节点，直接返回
        if (visited.contains(stmt)) {
            return;
        }
        
        // 标记为已访问
        visited.add(stmt);
        
        if (!stmt.getChildren().isEmpty()) {
            // 非叶子节点，递归处理其子节点
            for (CFGStmtNode child : stmt.getChildren()) {
                getAllLeafNodeHelper(child, result, visited);
            }
        } else {
            // 叶子节点，添加到结果列表
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
            // 打印 IN 和 OUT
            traverseTreeHelper(child);
        }
    }

    private void updateNewFuncCallEdge(CFGFuncNode newFuncNode,CFGStmtNode stmt){
        if (stmt.getType() == CFGStmtNode.StmtType.CALL){
            // 遍历所有函数名进行匹配
            for (String funcName : callGraph.getFuncNames()) {
                // 构建正则表达式模式 - 函数名前后不能是字母数字下划线
                String pattern = "(?<![\\w_])" + funcName + "(?![\\w_])";
                // 如果找到匹配
                if (stmt.getContent().matches(".*" + pattern + ".*")) {
                    // 找到对应的目标函数节点
                    CFGFuncNode targetFunc = null;
                    for (CFGFuncNode fn : callGraph.getFuncNodes()) {
                        if (fn.getFuncName().equals(funcName)) {
                            targetFunc = fn;
                            break;
                        }
                    }
                    if (targetFunc != null) {
                        // 检查这条边是否已经存在
                        boolean edgeExists = false;
                        // 假设 callGraph 有一个 getCallEdges() 方法返回 Collection<CFGCALLEdge>
                        // 并且 CFGCALLEdge 有 getSourceNode(), getCallerFunc(), getCalledFunc() 方法
                        if (callGraph.getCallEdges() != null) { // 防御性检查
                            for (CFGCALLEdge existingEdge : callGraph.getCallEdges()) {
                                if (existingEdge.getSource() == stmt &&
                                    existingEdge.getSourceFunc() == newFuncNode &&
                                    existingEdge.getTarget() == targetFunc) {
                                    // 如果参数和返回值也可能变化并影响边的唯一性，也需要在这里比较
                                    edgeExists = true;
                                    break;
                                }
                            }
                        }

                        if (!edgeExists) {
                            // 创建新的调用边
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
        // 分情况讨论：
        if (flag) {
            // 如果已经切分过，则需要切分本函数
            cuttedFunc.add(funcNode);
        } else {
            // 没有切分过，不需要切分
            if (intersection.isEmpty()){
                // 没冲突，不需要切割
                for (CFGStmtNode child : stmt.getChildren()){
                    checkCuttedFuncHelper(funcNode, child);
                }
            } else {
                // 有冲突，需要切割
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
        // 若 tempVars 为 a, b, c
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
        // callsite = "func(args)" 将 args 提取出来写为 <<>>
        int start = callsite.indexOf("(");
        // 检查是否找到了 '('
        if (start != -1) {
            // 查找最后一个 ')'
            int end = callsite.lastIndexOf(")");
            // 确保找到了 ')' 并且它在 '(' 之后
            if (end != -1 && end > start) {
                arguments += callsite.substring(start + 1, end);
            }
            // 如果没有找到匹配的 ')' 或者 ')' 在 '(' 之前，则参数部分为空字符串
        }
        // 如果没有找到 '('，则参数部分为空字符串
        arguments += ">>";
        String stackStr = "/\\ stack' = [backsite |-> \"" + funcNode.getFuncName() + "\", args |-> " + arguments + ", info |-> info']";
        return stackStr;
    }

    private void updateNewFuncTempVars (CFGFuncNode newFuncNode, Set<String> temp)  {
        if (temp.isEmpty()){
            return;
        }
        // 检查 newFuncNode 中的所有 CFGStmtNode
        // 如果有语句中使用了 tempVars 中的变量，则将该变量改为 info 中的变量，匹配规则是 var 字符串前后非字母数字下划线，则视为匹配成功
        // Example: 使用了 a 变量，替换为 info.temp.a
        List<CFGStmtNode> StmtNodelist = new ArrayList<>(newFuncNode.getRoot().getChildren());
        while (!StmtNodelist.isEmpty()){
            CFGStmtNode stmt = StmtNodelist.remove(0);
            String content = stmt.getContent();
            for (String var : temp) {
                String pattern = "(?<!\\w)(?<!info\\.temp\\.)" + var + "(?!\\w)";       // NEW, using var directly

                // System.err.println("content: " + content);
                // System.err.println("var: " + var);
                // 在正则表达式的开头添加 (?s) 标志，使 . (点号) 可以匹配包括换行符在内的任意字符
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
        // TODO: 对于每个函数，将叶子结点的 OutVar 取并集则为该函数的 VarChange
        for (CFGFuncNode funcNode : callGraph.getFuncNodes()){
            Set<String> varChange = new HashSet<>();
            List<CFGStmtNode> leafNodes = getAllLeafNode(funcNode.getRoot());
            for (CFGStmtNode leafNode : leafNodes){
                varChange.addAll(leafNode.OutVar);
            }
            funcVarChange.put(funcNode.getFuncName(), varChange);
        }
    }
}